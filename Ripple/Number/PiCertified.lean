/-
  Ripple.Number.PiCertified — π/4 is LPP-computable

  Builds a `CertifiedBoundedTimeComputable` witness for π/4 on top of the
  existing `Ripple.Number.Pi` construction (closed-form trajectory +
  convergence via the arctan addition formula) and pairs it with a
  `PolyCRNDecomposition` that splits the PIVP vector field into
  production/degradation polynomials with non-negative rational
  coefficients. Applying `bounded_crn_is_lpp_computable`
  concludes `IsLPPComputable (π / 4)` — with no dual-rail detour.

  Construction (matches `piPIVP` in `Ripple.Number.Pi`):
    field₀ := −X₀                       (w' = −w)
    field₁ := −2·X₀·X₁·X₂                (x' = −2wxy)
    field₂ := X₀·X₁²  −  X₀·X₂²          (y' = wx² − wy²)
    field₃ := X₀·X₁                      (z' = wx)
    init   := (1, 1, 0, 0),  output := 3.

  Production/degradation split:
    prod₀ := 0;                 degr₀ := 1                       (w' = 0 − 1·w)
    prod₁ := 0;                 degr₁ := 2·X₀·X₂                  (x' = 0 − 2wy·x)
    prod₂ := X₀·X₁²;            degr₂ := X₀·X₂                    (y' = wx² − wy·y)
    prod₃ := X₀·X₁;             degr₃ := 0                        (z' = wx − 0·z)

  All monomial coefficients lie in {0, 1, 2} ⊂ ℚ≥0 and all initial
  concentrations are in {0, 1}.
-/

import Ripple.Number.Pi
import Ripple.LPP.BoundedLPP

namespace Ripple.Number

open Ripple
open MvPolynomial
open Real

/-! ## The syntactic PolyPIVP for π/4 -/

/-- The syntactic `PolyPIVP 4` whose semantic image is `piPIVP`. -/
noncomputable def piPolyPIVP : PolyPIVP 4 where
  field := fun i =>
    match i with
    | 0 => - X 0
    | 1 => - (C 2) * X 0 * X 1 * X 2
    | 2 => X 0 * X 1 ^ 2 - X 0 * X 2 ^ 2
    | 3 => X 0 * X 1
  init := fun i =>
    match i with
    | 0 => 1
    | 1 => 1
    | 2 => 0
    | 3 => 0
  output := 3

/-! ## Syntactic field equals semantic field -/

/-- The evaluated polynomial field matches the semantic `piPIVP` field. -/
theorem piPolyPIVP_evalField_eq (x : Fin 4 → ℝ) (i : Fin 4) :
    piPolyPIVP.toPIVP.field x i = piPIVP.field x i := by
  show piPolyPIVP.evalField x i = piPIVP.field x i
  unfold PolyPIVP.evalField
  fin_cases i
  · show ((- X 0 : MvPolynomial (Fin 4) ℚ)).eval₂ (Rat.castHom ℝ) x = piPIVP.field x 0
    simp only [MvPolynomial.eval₂_neg, MvPolynomial.eval₂_X]
    simp [piPIVP]
  · show ((- (C 2) * X 0 * X 1 * X 2 : MvPolynomial (Fin 4) ℚ)).eval₂
          (Rat.castHom ℝ) x = piPIVP.field x 1
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_neg, MvPolynomial.eval₂_C,
      MvPolynomial.eval₂_X]
    simp [piPIVP]
    try ring
  · show ((X 0 * X 1 ^ 2 - X 0 * X 2 ^ 2 : MvPolynomial (Fin 4) ℚ)).eval₂
          (Rat.castHom ℝ) x = piPIVP.field x 2
    simp only [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
      MvPolynomial.eval₂_X]
    simp [piPIVP]
  · show ((X 0 * X 1 : MvPolynomial (Fin 4) ℚ)).eval₂ (Rat.castHom ℝ) x = piPIVP.field x 3
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    simp [piPIVP]

/-- Initial condition matches. -/
theorem piPolyPIVP_init_eq (i : Fin 4) :
    (piPolyPIVP.toPIVP.init i : ℝ) = piPIVP.init i := by
  show ((piPolyPIVP.init i : ℚ) : ℝ) = piPIVP.init i
  fin_cases i <;> simp [piPolyPIVP, piPIVP]

/-! ## CertifiedBoundedTimeComputable witness -/

/-- Continuity of the closed-form solution: each component is a composition
of exp, polynomial, division (denominator > 0) and arctan. -/
theorem piSolution_continuous : Continuous piSolution := by
  apply continuous_pi
  intro i
  fin_cases i
  · -- w = exp(-t)
    change Continuous fun t => piSolution t 0
    simp only [pi_sol_w]
    exact Real.continuous_exp.comp continuous_neg
  · -- x = 1 / ((1 - exp(-t))² + 1)
    change Continuous fun t => piSolution t 1
    simp only [pi_sol_x]
    refine continuous_const.div ?_ (fun t => by positivity)
    exact ((continuous_const.sub (Real.continuous_exp.comp continuous_neg)).pow 2).add
      continuous_const
  · -- y = (1 - exp(-t)) / ((1 - exp(-t))² + 1)
    change Continuous fun t => piSolution t 2
    simp only [pi_sol_y]
    refine (continuous_const.sub (Real.continuous_exp.comp continuous_neg)).div ?_
      (fun t => by positivity)
    exact ((continuous_const.sub (Real.continuous_exp.comp continuous_neg)).pow 2).add
      continuous_const
  · -- z = arctan(1 - exp(-t))
    change Continuous fun t => piSolution t 3
    simp only [pi_sol_z]
    exact Real.continuous_arctan.comp
      (continuous_const.sub (Real.continuous_exp.comp continuous_neg))

/-- `piSolution` is a semantic solution of `piPolyPIVP.toPIVP`. We reuse the
derivative chain of `Ripple.Number.Pi`, rewriting the
syntactic field to the semantic field via `piPolyPIVP_evalField_eq`. -/
noncomputable def piPolySolution : PIVP.Solution piPolyPIVP.toPIVP where
  trajectory := piSolution
  init_cond := by
    funext i
    rw [pi_sol_init]
    -- Both sides equal piPIVP.init i; we must show piPolyPIVP.toPIVP.init = piPIVP.init.
    rw [piPolyPIVP_init_eq]
  is_solution := fun t _ => by
    -- Reduce syntactic field evaluation to semantic field evaluation.
    have hfield_eq : piPolyPIVP.toPIVP.field (piSolution t) = piPIVP.field (piSolution t) := by
      funext i; exact piPolyPIVP_evalField_eq _ i
    rw [hfield_eq]
    -- Now reprove the derivative statement against piPIVP.field, which is the
    -- same derivation as for `piPIVP`.
    set u := 1 - exp (-t) with hu_def
    have hfield : piPIVP.field (piSolution t) =
        ![-exp (-t), -2 * exp (-t) * (1 / (u ^ 2 + 1)) * (u / (u ^ 2 + 1)),
          exp (-t) * (1 / (u ^ 2 + 1)) ^ 2 - exp (-t) * (u / (u ^ 2 + 1)) ^ 2,
          exp (-t) * (1 / (u ^ 2 + 1))] := by
      ext i; fin_cases i <;>
        simp [piPIVP, piSolution, Matrix.cons_val_zero, Matrix.cons_val_one,
          hu_def]
    rw [hfield, hasDerivAt_pi]
    have h_neg : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) t := by
      simpa [id] using (hasDerivAt_id t).neg
    have h_exp := h_neg.exp
    have h_u := (hasDerivAt_const t (1:ℝ)).sub h_exp
    have hu2_pos : u ^ 2 + 1 ≠ 0 := by positivity
    intro i; fin_cases i
    · change HasDerivAt (fun s => exp (-s)) (-exp (-t)) t
      convert h_exp using 1; ring
    · change HasDerivAt (fun s => 1 / ((1 - exp (-s)) ^ 2 + 1))
        (-2 * exp (-t) * (1 / (u ^ 2 + 1)) * (u / (u ^ 2 + 1))) t
      convert (hasDerivAt_const t (1:ℝ)).div
        (h_u.pow 2 |>.add (hasDerivAt_const t (1:ℝ))) hu2_pos using 1
      simp only [Pi.add_apply, Pi.pow_apply, Pi.sub_apply, hu_def]
      field_simp; ring
    · change HasDerivAt (fun s => (1 - exp (-s)) / ((1 - exp (-s)) ^ 2 + 1))
        (exp (-t) * (1 / (u ^ 2 + 1)) ^ 2 -
         exp (-t) * (u / (u ^ 2 + 1)) ^ 2) t
      convert h_u.div (h_u.pow 2 |>.add (hasDerivAt_const t (1:ℝ)))
        hu2_pos using 1
      simp only [Pi.add_apply, Pi.pow_apply, Pi.sub_apply, hu_def]
      field_simp; ring
    · change HasDerivAt (fun s => arctan (1 - exp (-s)))
        (exp (-t) * (1 / (u ^ 2 + 1))) t
      convert h_u.arctan using 1
      simp [Pi.sub_apply, hu_def]; ring

/-- Boundedness of `piSolution` transported through the syntactic/semantic
equivalence of fields. -/
theorem piPolyPIVP_bounded : piPolyPIVP.toPIVP.IsBounded piSolution := by
  -- `piPIVP.IsBounded piSolution` and `piPolyPIVP.toPIVP.IsBounded piSolution`
  -- are the same proposition (both unfold to: ∃ M > 0, ∀ t ≥ 0, ‖piSolution t‖ ≤ M).
  exact pi_bounded

/-- `CertifiedBoundedTimeComputable` witness for π/4. -/
noncomputable def piCBTC : CertifiedBoundedTimeComputable 4 (π / 4) where
  pivp := piPolyPIVP
  sol := piPolySolution
  modulus := fun r => (r : ℝ) + 1
  bounded := piPolyPIVP_bounded
  trajectory_continuous := piSolution_continuous
  convergence := by
    intro r t htr
    have hr_nn : (0 : ℝ) ≤ ↑r := Nat.cast_nonneg r
    have ht_pos : 0 ≤ t := by
      have h1 : (0 : ℝ) ≤ (r : ℝ) + 1 := by linarith
      linarith
    -- trajectory at output = piSolution t 3
    show |piSolution t piPolyPIVP.output - π / 4| < Real.exp (-(r : ℝ))
    have hout : piPolyPIVP.output = (3 : Fin 4) := rfl
    rw [hout]
    calc |piSolution t 3 - π / 4|
        ≤ exp (-t) := pi_convergence t ht_pos
      _ < exp (-(↑r + 1)) := by apply exp_lt_exp.mpr; linarith
      _ = exp (-(↑r : ℝ) - 1) := by ring_nf
      _ < exp (-(↑r : ℝ)) := by apply exp_lt_exp.mpr; linarith

/-- π/4 is real-time computable: `piCBTC` has modulus `r + 1`. -/
theorem pi_quarter_is_realtime : Ripple.IsRealTimeComputable (π / 4) :=
  ⟨4, piCBTC, 2, by norm_num, fun r => by
    change (r : ℝ) + 1 ≤ 2 * ((r : ℝ) + 1)
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    linarith⟩

/-- π is real-time computable ([RTCRN2] Thm 5): π = 4 · (π/4), product with the rational
constant 4. -/
theorem pi_is_realtime : Ripple.IsRealTimeComputable π := by
  have h := Ripple.realtime_field_mul (Ripple.realtime_rat_const 4) pi_quarter_is_realtime
  have h4 : ((4 : ℚ) : ℝ) * (π / 4) = π := by push_cast; ring
  rwa [h4] at h

/-! ## PolyCRNDecomposition witness -/

/-- Production polynomials: prod₀ = 0, prod₁ = 0, prod₂ = X₀·X₁², prod₃ = X₀·X₁. -/
noncomputable def piProd : Fin 4 → MvPolynomial (Fin 4) ℚ
  | 0 => 0
  | 1 => 0
  | 2 => X 0 * X 1 ^ 2
  | 3 => X 0 * X 1

/-- Degradation polynomials: degr₀ = 1, degr₁ = 2·X₀·X₂, degr₂ = X₀·X₂, degr₃ = 0. -/
noncomputable def piDegr : Fin 4 → MvPolynomial (Fin 4) ℚ
  | 0 => C 1
  | 1 => C 2 * X 0 * X 2
  | 2 => X 0 * X 2
  | 3 => 0

/-- Coefficients of a polynomial built from non-negative constants, X's, and
products/sums/powers are non-negative. -/
private lemma coeff_mul_nonneg {d : ℕ} (p q : MvPolynomial (Fin d) ℚ)
    (hp : ∀ σ, 0 ≤ p.coeff σ) (hq : ∀ σ, 0 ≤ q.coeff σ) :
    ∀ σ, 0 ≤ (p * q).coeff σ := by
  classical
  intro σ
  rw [MvPolynomial.coeff_mul]
  apply Finset.sum_nonneg
  intro ⟨a, b⟩ _
  exact mul_nonneg (hp a) (hq b)

private lemma coeff_pow_nonneg {d : ℕ} (p : MvPolynomial (Fin d) ℚ)
    (hp : ∀ σ, 0 ≤ p.coeff σ) (n : ℕ) :
    ∀ σ, 0 ≤ (p ^ n).coeff σ := by
  induction n with
  | zero => intro σ; simp [MvPolynomial.coeff_one]; split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ]
    exact coeff_mul_nonneg _ _ ih hp

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
theorem piProd_nonneg (i : Fin 4) (σ : Fin 4 →₀ ℕ) : 0 ≤ (piProd i).coeff σ := by
  fin_cases i
  · simp [piProd]
  · simp [piProd]
  · -- prod 2 = X 0 * X 1 ^ 2
    show 0 ≤ ((X 0 * X 1 ^ 2 : MvPolynomial (Fin 4) ℚ)).coeff σ
    exact coeff_mul_nonneg _ _ (coeff_X_nonneg 0)
      (coeff_pow_nonneg _ (coeff_X_nonneg 1) 2) σ
  · -- prod 3 = X 0 * X 1
    show 0 ≤ ((X 0 * X 1 : MvPolynomial (Fin 4) ℚ)).coeff σ
    exact coeff_mul_nonneg _ _ (coeff_X_nonneg 0) (coeff_X_nonneg 1) σ

/-- Non-negativity of degr coefficients. -/
theorem piDegr_nonneg (i : Fin 4) (σ : Fin 4 →₀ ℕ) : 0 ≤ (piDegr i).coeff σ := by
  fin_cases i
  · -- degr 0 = C 1
    show 0 ≤ ((C 1 : MvPolynomial (Fin 4) ℚ)).coeff σ
    exact coeff_C_nonneg (by norm_num) σ
  · -- degr 1 = C 2 * X 0 * X 2
    show 0 ≤ ((C 2 * X 0 * X 2 : MvPolynomial (Fin 4) ℚ)).coeff σ
    exact coeff_mul_nonneg _ _
      (coeff_mul_nonneg _ _ (coeff_C_nonneg (by norm_num)) (coeff_X_nonneg 0))
      (coeff_X_nonneg 2) σ
  · -- degr 2 = X 0 * X 2
    show 0 ≤ ((X 0 * X 2 : MvPolynomial (Fin 4) ℚ)).coeff σ
    exact coeff_mul_nonneg _ _ (coeff_X_nonneg 0) (coeff_X_nonneg 2) σ
  · -- degr 3 = 0
    simp [piDegr]

/-- Initial conditions are non-negative: 1, 1, 0, 0. -/
theorem piPolyPIVP_init_nonneg (i : Fin 4) : 0 ≤ piPolyPIVP.init i := by
  fin_cases i <;> simp [piPolyPIVP]

/-- Syntactic field decomposition: field_i = prod_i - degr_i * X_i. -/
theorem piPolyPIVP_field_eq (i : Fin 4) :
    piPolyPIVP.field i = piProd i - piDegr i * MvPolynomial.X i := by
  fin_cases i
  · -- field 0 = - X 0 = 0 - C 1 * X 0
    show (- X 0 : MvPolynomial (Fin 4) ℚ) = 0 - C 1 * X 0
    rw [MvPolynomial.C_1]; ring
  · -- field 1 = - (C 2) * X 0 * X 1 * X 2 = 0 - (C 2 * X 0 * X 2) * X 1
    show (- (C 2) * X 0 * X 1 * X 2 : MvPolynomial (Fin 4) ℚ) =
      0 - (C 2 * X 0 * X 2) * X 1
    ring
  · -- field 2 = X 0 * X 1 ^ 2 - X 0 * X 2 ^ 2 = X 0 * X 1 ^ 2 - (X 0 * X 2) * X 2
    show (X 0 * X 1 ^ 2 - X 0 * X 2 ^ 2 : MvPolynomial (Fin 4) ℚ) =
      X 0 * X 1 ^ 2 - X 0 * X 2 * X 2
    ring
  · -- field 3 = X 0 * X 1 = X 0 * X 1 - 0 * X 3
    show (X 0 * X 1 : MvPolynomial (Fin 4) ℚ) = X 0 * X 1 - 0 * X 3
    ring

/-- `PolyCRNDecomposition` witness for `piPolyPIVP`. -/
noncomputable def piPCD : PolyCRNDecomposition 4 piPolyPIVP where
  prod := piProd
  degr := piDegr
  prod_nonneg := piProd_nonneg
  degr_nonneg := piDegr_nonneg
  init_nonneg := piPolyPIVP_init_nonneg
  field_eq := piPolyPIVP_field_eq

/-! ## Main theorem: π/4 is LPP-computable -/

/-- `π/4 ∈ [0, 1]`: lower bound by positivity, upper bound by `π < 4`. -/
private theorem pi_quarter_in_unit : 0 ≤ π / 4 ∧ π / 4 ≤ 1 := by
  refine ⟨?_, ?_⟩
  · exact div_nonneg Real.pi_pos.le (by norm_num)
  · rw [div_le_one (by norm_num : (0:ℝ) < 4)]
    linarith [Real.pi_lt_four]

/-- **π/4 is LPP-computable** via the direct bounded-CRN-computable route
(no dual-rail). -/
theorem pi_quarter_is_lpp_computable : IsLPPComputable (π / 4) :=
  bounded_crn_is_lpp_computable pi_quarter_in_unit piCBTC piPCD

end Ripple.Number
