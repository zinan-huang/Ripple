/-
  Ripple.Number.InvECertified — 1/e is LPP-computable

  Builds a `CertifiedBoundedTimeComputable` witness for `1/e = exp (-1)`
  on a fresh 2-dimensional PIVP (distinct from `eulerPIVP`, which computes
  `e = exp 1 ∉ [0, 1]` and is therefore not directly usable with the LPP
  unit-interval requirement).

  Derivation: set `z := 1/y` where `y` solves Euler's system. Then
  `z' = -y'/y² = -(x·y)/y² = -x·z` with `z(0) = 1/1 = 1`, and the
  closed-form `z(t) = exp(exp(-t) - 1)` satisfies `z(t) → exp(-1) = 1/e`
  exponentially as `t → ∞`.

  Construction:
    field₀ := - X 0                   (x' = -x)
    field₁ := - (X 0 * X 1)           (z' = -x·z)
    init   := (1, 1),  output := 1.

  Production/degradation split:
    prod₀ := 0;        degr₀ := C 1             (x' = 0 − 1·x)
    prod₁ := 0;        degr₁ := X 0             (z' = 0 − X₀·z)

  All monomial coefficients lie in {0, 1} ⊂ ℚ≥0; initial concentrations
  lie in {1}.
-/

import Ripple.Core.BoundedTime
import Ripple.LPP.BoundedLPP
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace Ripple.Number

open Ripple
open MvPolynomial
open Real

/-! ## The syntactic PolyPIVP for 1/e -/

/-- The syntactic `PolyPIVP 2` whose semantic image corresponds to the
`x' = -x, z' = -x·z` system with `x(0) = z(0) = 1`. -/
noncomputable def invEPolyPIVP : PolyPIVP 2 where
  field := fun i =>
    match i with
    | 0 => - X 0
    | 1 => - (X 0 * X 1)
  init := fun i =>
    match i with
    | 0 => 1
    | 1 => 1
  output := 1

/-- Closed-form solution: `x(t) = exp(-t)`, `z(t) = exp(exp(-t) - 1)`. -/
noncomputable def invESolution : ℝ → Fin 2 → ℝ :=
  fun t => ![exp (-t), exp (exp (-t) - 1)]

/-! ## Componentwise closed forms -/

theorem invE_sol_x (t : ℝ) : invESolution t 0 = exp (-t) := by
  simp [invESolution, Matrix.cons_val_zero]

theorem invE_sol_z (t : ℝ) : invESolution t 1 = exp (exp (-t) - 1) := by
  simp [invESolution, Matrix.cons_val_one]

/-! ## Syntactic field = semantic field -/

theorem invEPolyPIVP_evalField_eq (x : Fin 2 → ℝ) (i : Fin 2) :
    invEPolyPIVP.toPIVP.field x i =
      (match i with
        | (0 : Fin 2) => - x 0
        | (1 : Fin 2) => - (x 0 * x 1)) := by
  show invEPolyPIVP.evalField x i = _
  unfold PolyPIVP.evalField
  fin_cases i
  · show ((- X 0 : MvPolynomial (Fin 2) ℚ)).eval₂ (Rat.castHom ℝ) x = - x 0
    simp [MvPolynomial.eval₂_neg, MvPolynomial.eval₂_X]
  · show ((- (X 0 * X 1) : MvPolynomial (Fin 2) ℚ)).eval₂
          (Rat.castHom ℝ) x = - (x 0 * x 1)
    simp [MvPolynomial.eval₂_neg, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_X]

/-- Initial condition matches. -/
theorem invEPolyPIVP_init_eq (i : Fin 2) :
    invEPolyPIVP.toPIVP.init i = invESolution 0 i := by
  fin_cases i
  · show ((invEPolyPIVP.init 0 : ℚ) : ℝ) = invESolution 0 0
    simp [invEPolyPIVP, invESolution, Matrix.cons_val_zero]
  · show ((invEPolyPIVP.init 1 : ℚ) : ℝ) = invESolution 0 1
    simp [invEPolyPIVP, invESolution, Matrix.cons_val_one]

/-! ## Boundedness and sign lemmas -/

theorem invE_x_pos (t : ℝ) : 0 < invESolution t 0 := by
  rw [invE_sol_x]; exact exp_pos _

theorem invE_x_le_one {t : ℝ} (ht : 0 ≤ t) : invESolution t 0 ≤ 1 := by
  rw [invE_sol_x, ← exp_zero]
  exact exp_le_exp.mpr (neg_nonpos.mpr ht)

theorem invE_z_pos (t : ℝ) : 0 < invESolution t 1 := by
  rw [invE_sol_z]; exact exp_pos _

theorem invE_z_le_one {t : ℝ} (ht : 0 ≤ t) : invESolution t 1 ≤ 1 := by
  rw [invE_sol_z]
  have h1 : exp (-t) ≤ 1 := by
    rw [← exp_zero]; exact exp_le_exp.mpr (neg_nonpos.mpr ht)
  have h2 : exp (-t) - 1 ≤ 0 := by linarith
  calc exp (exp (-t) - 1) ≤ exp 0 := exp_le_exp.mpr h2
    _ = 1 := exp_zero

/-- `invESolution` is bounded by `2` on `t ≥ 0`. -/
theorem invE_bounded : invEPolyPIVP.toPIVP.IsBounded invESolution := by
  refine ⟨2, by norm_num, ?_⟩
  intro t ht
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  intro i
  fin_cases i
  · -- component 0: exp(-t) ≤ 1 ≤ 2
    simp [invESolution, Matrix.cons_val_zero,
      norm_of_nonneg (le_of_lt (exp_pos _))]
    calc exp (-t) ≤ 1 := by
            rw [← exp_zero]; exact exp_le_exp.mpr (neg_nonpos.mpr ht)
      _ ≤ 2 := by norm_num
  · -- component 1: exp(exp(-t) - 1) ≤ 1 ≤ 2
    simp [invESolution, Matrix.cons_val_one,
      norm_of_nonneg (le_of_lt (exp_pos _))]
    have h1 : exp (-t) ≤ 1 := by
      rw [← exp_zero]; exact exp_le_exp.mpr (neg_nonpos.mpr ht)
    have h2 : exp (-t) - 1 ≤ 0 := by linarith
    calc exp (exp (-t) - 1) ≤ exp 0 := exp_le_exp.mpr h2
      _ = 1 := exp_zero
      _ ≤ 2 := by norm_num

/-! ## Convergence estimate -/

/-- Key real-analytic lemma: for `u ∈ [0, 1]`, `exp u - 1 ≤ u · exp 1`.

Proof: let `g(u) := u · exp 1 − (exp u − 1)`. Then `g 0 = 0` and
`g'(u) = exp 1 − exp u ≥ 0` on `[0, 1]`. Hence `g` is monotone on
`[0, 1]`, so `g(u) ≥ g(0) = 0` for `u ∈ [0, 1]`. -/
private lemma exp_sub_one_le_mul_exp_one {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    exp u - 1 ≤ u * exp 1 := by
  -- Define g(u) := u * exp 1 - (exp u - 1); show g 0 = 0 and g'(u) ≥ 0
  -- on [0, 1].  Use `Convex.inner_le_iff`? Simpler: direct `StrictMonoOn`
  -- via mean-value — we invoke `Convex.inner_le_iff` is overkill.
  -- Use: h(u) := exp 1 * u - exp u + 1. h(0) = 0. h'(u) = exp 1 - exp u.
  -- On [0,1], h'(u) ≥ 0, so h monotone ⇒ h(u) ≥ 0.
  set g : ℝ → ℝ := fun u => u * exp 1 - (exp u - 1) with hg_def
  have hg0 : g 0 = 0 := by simp [g]
  have hg_mono : MonotoneOn g (Set.Icc 0 1) := by
    -- Use StrictMonoOn_of_hasDerivWithin_pos or MonotoneOn via HasDerivAt.
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
    · -- continuous
      refine Continuous.continuousOn ?_
      exact (continuous_id.mul continuous_const).sub
        (Real.continuous_exp.sub continuous_const)
    · -- differentiable on interior
      intro x _
      refine DifferentiableAt.differentiableWithinAt ?_
      exact (differentiableAt_id.mul_const _).sub
        (Real.differentiable_exp.differentiableAt.sub_const _)
    · -- deriv nonneg on interior
      intro x hx
      rw [interior_Icc] at hx
      have hx1 : x < 1 := (Set.mem_Ioo.mp hx).2
      have hderiv : HasDerivAt g (exp 1 - exp x) x := by
        have h1 : HasDerivAt (fun u : ℝ => u * exp 1) (exp 1) x := by
          simpa using (hasDerivAt_id x).mul_const (exp 1)
        have h2 : HasDerivAt (fun u : ℝ => exp u - 1) (exp x) x := by
          simpa using (Real.hasDerivAt_exp x).sub_const 1
        simpa [g] using h1.sub h2
      rw [hderiv.deriv]
      have : exp x ≤ exp 1 := exp_le_exp.mpr hx1.le
      linarith
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0:ℝ) 1 := by simp
  have hmemu : u ∈ Set.Icc (0:ℝ) 1 := ⟨hu0, hu1⟩
  have := hg_mono hmem0 hmemu hu0
  -- this : g 0 ≤ g u
  rw [hg0] at this
  -- this : 0 ≤ u * exp 1 - (exp u - 1)
  linarith

/-- `|z(t) - 1/e| ≤ exp(-t)` for `t ≥ 0`.

Proof: let `u := exp(-t) ∈ (0, 1]`. Then
  z(t) - 1/e = exp(u - 1) - exp(-1) = exp(-1) · (exp u - 1)  ≥ 0.
Using `exp u - 1 ≤ u · exp 1` on `[0, 1]`:
  |z(t) - 1/e| = exp(-1) · (exp u - 1) ≤ exp(-1) · u · exp 1 = u = exp(-t). -/
theorem invE_convergence (t : ℝ) (ht : 0 ≤ t) :
    |invESolution t 1 - 1 / exp 1| ≤ exp (-t) := by
  rw [invE_sol_z]
  set u := exp (-t) with hu_def
  have hu_pos : 0 < u := exp_pos _
  have hu_nn : 0 ≤ u := hu_pos.le
  have hu_le : u ≤ 1 := by
    rw [hu_def, ← exp_zero]; exact exp_le_exp.mpr (neg_nonpos.mpr ht)
  -- Factor: exp(u - 1) = exp(-1) * exp u.
  have hfactor : exp (u - 1) = exp (-1) * exp u := by
    rw [← exp_add]; ring_nf
  -- 1/e = exp(-1)
  have hinv : (1 : ℝ) / exp 1 = exp (-1) := by
    rw [one_div, ← exp_neg]
  rw [hinv, hfactor]
  -- Goal: |exp(-1) * exp u - exp(-1)| ≤ u
  -- Factor exp(-1):
  have : exp (-1) * exp u - exp (-1) = exp (-1) * (exp u - 1) := by ring
  rw [this]
  -- Since exp u ≥ 1 (u ≥ 0), exp u - 1 ≥ 0, and exp(-1) > 0.
  have h_exp_u_ge : 1 ≤ exp u := by
    rw [← exp_zero]; exact exp_le_exp.mpr hu_nn
  have h_fac_nn : 0 ≤ exp (-1) * (exp u - 1) :=
    mul_nonneg (le_of_lt (exp_pos _)) (by linarith)
  rw [abs_of_nonneg h_fac_nn]
  -- exp u - 1 ≤ u * exp 1
  have hbound : exp u - 1 ≤ u * exp 1 := exp_sub_one_le_mul_exp_one hu_nn hu_le
  have : exp (-1) * (exp u - 1) ≤ exp (-1) * (u * exp 1) :=
    mul_le_mul_of_nonneg_left hbound (le_of_lt (exp_pos _))
  have hsimp : exp (-1) * (u * exp 1) = u := by
    have he1 : exp (-1) * exp 1 = 1 := by rw [← exp_add]; simp
    calc exp (-1) * (u * exp 1)
        = (exp (-1) * exp 1) * u := by ring
      _ = u := by rw [he1]; ring
  linarith [this, hsimp.ge, hsimp.le]

/-! ## Solution bundle -/

/-- `invESolution` is continuous: exp of continuous is continuous. -/
theorem invESolution_continuous : Continuous invESolution := by
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous fun t => invESolution t 0
    simp only [invE_sol_x]
    exact Real.continuous_exp.comp continuous_neg
  · change Continuous fun t => invESolution t 1
    simp only [invE_sol_z]
    exact Real.continuous_exp.comp
      ((Real.continuous_exp.comp continuous_neg).sub continuous_const)

/-- `invESolution` is a semantic solution of `invEPolyPIVP.toPIVP`. -/
noncomputable def invEPolySolution : PIVP.Solution invEPolyPIVP.toPIVP where
  trajectory := invESolution
  init_cond := by
    funext i
    exact (invEPolyPIVP_init_eq i).symm
  is_solution := fun t _ => by
    -- Rewrite the syntactic field to the explicit form.
    have hfield : invEPolyPIVP.toPIVP.field (invESolution t) =
        ![- exp (-t), - (exp (-t) * exp (exp (-t) - 1))] := by
      ext i
      rw [invEPolyPIVP_evalField_eq]
      fin_cases i
      · simp [invESolution, Matrix.cons_val_zero]
      · simp [invESolution, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hfield, hasDerivAt_pi]
    have h_neg : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) t := by
      simpa [id] using (hasDerivAt_id t).neg
    have h_exp_neg : HasDerivAt (fun s : ℝ => exp (-s)) (-exp (-t)) t := by
      convert h_neg.exp using 1; ring
    intro i; fin_cases i
    · -- d/dt exp(-t) = -exp(-t)
      change HasDerivAt (fun s => exp (-s)) (-exp (-t)) t
      exact h_exp_neg
    · -- d/dt exp(exp(-t) - 1) = exp(-t) * ... wait, compute:
      -- Let f(t) = exp(exp(-t) - 1). Then f'(t) = exp(exp(-t) - 1) * d/dt(exp(-t) - 1)
      -- = exp(exp(-t) - 1) * (-exp(-t)) = -(exp(-t) * exp(exp(-t) - 1))
      change HasDerivAt (fun s => exp (exp (-s) - 1))
        (- (exp (-t) * exp (exp (-t) - 1))) t
      have h_inner : HasDerivAt (fun s : ℝ => exp (-s) - 1) (-exp (-t)) t := by
        have := h_exp_neg.sub_const (1 : ℝ)
        exact this
      have h_comp := h_inner.exp
      -- h_comp : HasDerivAt (fun s => exp (exp (-s) - 1)) (-exp(-t) * exp(exp(-t) - 1)) t
      convert h_comp using 1
      ring

/-! ## CertifiedBoundedTimeComputable witness -/

/-- `CertifiedBoundedTimeComputable` witness for `1/e`. -/
noncomputable def invECBTC : CertifiedBoundedTimeComputable 2 (1 / exp 1) where
  pivp := invEPolyPIVP
  sol := invEPolySolution
  modulus := fun r => (r : ℝ) + 1
  bounded := invE_bounded
  trajectory_continuous := invESolution_continuous
  convergence := by
    intro r t htr
    have hr_nn : (0 : ℝ) ≤ ↑r := Nat.cast_nonneg r
    have ht_pos : 0 ≤ t := by
      have : (0 : ℝ) ≤ (r : ℝ) + 1 := by linarith
      linarith
    show |invESolution t invEPolyPIVP.output - 1 / exp 1| < Real.exp (-(r : ℝ))
    have hout : invEPolyPIVP.output = (1 : Fin 2) := rfl
    rw [hout]
    calc |invESolution t 1 - 1 / exp 1|
        ≤ exp (-t) := invE_convergence t ht_pos
      _ < exp (-(↑r + 1)) := by apply exp_lt_exp.mpr; linarith
      _ = exp (-(↑r : ℝ) - 1) := by ring_nf
      _ < exp (-(↑r : ℝ)) := by apply exp_lt_exp.mpr; linarith

/-! ## PolyCRNDecomposition witness -/

/-- Production polynomials: prod₀ = 0, prod₁ = 0. -/
noncomputable def invEProd : Fin 2 → MvPolynomial (Fin 2) ℚ
  | 0 => 0
  | 1 => 0

/-- Degradation polynomials: degr₀ = C 1, degr₁ = X 0. -/
noncomputable def invEDegr : Fin 2 → MvPolynomial (Fin 2) ℚ
  | 0 => C 1
  | 1 => X 0

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

theorem invEProd_nonneg (i : Fin 2) (σ : Fin 2 →₀ ℕ) :
    0 ≤ (invEProd i).coeff σ := by
  fin_cases i
  · simp [invEProd]
  · simp [invEProd]

theorem invEDegr_nonneg (i : Fin 2) (σ : Fin 2 →₀ ℕ) :
    0 ≤ (invEDegr i).coeff σ := by
  fin_cases i
  · show 0 ≤ ((C 1 : MvPolynomial (Fin 2) ℚ)).coeff σ
    exact coeff_C_nonneg (by norm_num) σ
  · show 0 ≤ ((X 0 : MvPolynomial (Fin 2) ℚ)).coeff σ
    exact coeff_X_nonneg 0 σ

theorem invEPolyPIVP_init_nonneg (i : Fin 2) : 0 ≤ invEPolyPIVP.init i := by
  fin_cases i <;> simp [invEPolyPIVP]

/-- Syntactic field decomposition: field_i = prod_i - degr_i · X_i. -/
theorem invEPolyPIVP_field_eq (i : Fin 2) :
    invEPolyPIVP.field i = invEProd i - invEDegr i * MvPolynomial.X i := by
  fin_cases i
  · show (- X 0 : MvPolynomial (Fin 2) ℚ) = 0 - C 1 * X 0
    rw [MvPolynomial.C_1]; ring
  · show (- (X 0 * X 1) : MvPolynomial (Fin 2) ℚ) = 0 - X 0 * X 1
    ring

/-- `PolyCRNDecomposition` witness for `invEPolyPIVP`. -/
noncomputable def invEPCD : PolyCRNDecomposition 2 invEPolyPIVP where
  prod := invEProd
  degr := invEDegr
  prod_nonneg := invEProd_nonneg
  degr_nonneg := invEDegr_nonneg
  init_nonneg := invEPolyPIVP_init_nonneg
  field_eq := invEPolyPIVP_field_eq

/-! ## Main theorem: 1/e is LPP-computable -/

/-- `1/e ∈ [0, 1]`: lower bound by positivity, upper bound by `1 ≤ e`. -/
private theorem inv_e_in_unit : 0 ≤ 1 / exp 1 ∧ 1 / exp 1 ≤ 1 := by
  refine ⟨?_, ?_⟩
  · exact le_of_lt (by positivity)
  · rw [div_le_one (exp_pos 1)]
    have : (1 : ℝ) ≤ exp 1 := by
      rw [← exp_zero]; exact exp_le_exp.mpr (by norm_num)
    exact this

/-- **1/e is LPP-computable** via the direct bounded-CRN-computable route
(no dual-rail). -/
theorem inv_e_is_lpp_computable : ∃ _ : IsLPPComputable (1 / exp 1), True :=
  bounded_crn_is_lpp_computable_unconditional inv_e_in_unit invECBTC invEPCD

end Ripple.Number
