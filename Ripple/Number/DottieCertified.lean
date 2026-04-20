/-
  Ripple.Number.DottieCertified — The Dottie number is LPP-computable.

  Stages 2-4 of the Dottie pipeline, chained on top of `dottieBTC` from
  `Ripple.Number.Dottie`:

    Stage 2 (init shift):
      The existing `dottiePolyPIVP` has non-zero initial condition `(0, 1, 0)`.
      `Tier1Composition.btc_to_cbtc_pcd_of_unit_interval` requires zero init.
      Reparametrize via `u₁ := Y − 1` so that the shifted initial condition is
      `(0, 0, 0)`. New coordinates:
          u₀ := x            u₀(0) = 0
          u₁ := Y − 1        u₁(0) = 0
          u₂ := Z            u₂(0) = 0
      Shifted vector field (all polynomial over ℚ in u₀, u₁, u₂):
          u₀' = (u₁ + 1) − u₀ = u₁ − u₀ + 1
          u₁' = Y' = Z·(x − Y) = u₂·u₀ − u₂·u₁ − u₂
          u₂' = Z' = Y·(Y − x) = (u₁ + 1)² − (u₁ + 1)·u₀
                                = u₁² + 2·u₁ + 1 − u₀·u₁ − u₀

      Build `dottieShiftedPolyPIVP : PolyPIVP 3` with these polynomials, the
      shifted initial condition, and output index `0`. Since the output is
      still the `x` coordinate, its convergence to `dottieNumber` is inherited
      verbatim from `dottieScalarSol_convergence`.

    Stage 3 (Tier 1 composition): apply `btc_to_cbtc_pcd_of_unit_interval` to
      lift the shifted `BoundedTimeComputable` to a
      `CertifiedBoundedTimeComputable + PolyCRNDecomposition` pair.

    Stage 4 (bounded-CRN ⇒ LPP): apply
      `bounded_crn_is_lpp_computable_unconditional` to conclude
      `IsLPPComputable dottieNumber`.
-/

import Ripple.Number.Dottie
import Ripple.DualRail.Tier1Composition
import Ripple.LPP.BoundedLPP

namespace Ripple.Number

open Ripple
open MvPolynomial
open Real

/-! ## The shifted PolyPIVP (zero-init variant of `dottiePolyPIVP`)

  State `(u₀, u₁, u₂) = (x, Y − 1, Z)`. The original field on `(x, Y, Z)` is
    x' = Y − x,  Y' = Z·(x − Y),  Z' = Y·(Y − x).
  Substituting `Y = u₁ + 1` yields the shifted field:
    u₀' = u₁ − u₀ + 1
    u₁' = u₂·u₀ − u₂·u₁ − u₂
    u₂' = u₁² + 2·u₁ + 1 − u₀·u₁ − u₀.
-/

/-- The shifted (zero-init) syntactic polynomial PIVP for the Dottie number. -/
noncomputable def dottieShiftedPolyPIVP : Ripple.PolyPIVP 3 where
  field := fun i =>
    match i with
    | ⟨0, _⟩ => X 1 - X 0 + C 1
    | ⟨1, _⟩ => X 2 * X 0 - X 2 * X 1 - X 2
    | ⟨2, _⟩ => X 1 * X 1 + C 2 * X 1 + C 1 - X 0 * X 1 - X 0
    | ⟨n+3, hn⟩ => absurd hn (by omega)
  init := ![0, 0, 0]
  output := 0

/-! ## The shifted trajectory
   `dottieShiftedTrajectory t = (x(t), cos(x(t)) − 1, sin(x(t)))`, i.e. the
   original Dottie trajectory with the second coordinate shifted down by 1.
-/

/-- Shifted trajectory. -/
noncomputable def dottieShiftedTrajectory : ℝ → Fin 3 → ℝ := fun t =>
  ![dottieScalarSol t, Real.cos (dottieScalarSol t) - 1, Real.sin (dottieScalarSol t)]

@[simp] lemma dottieShiftedTrajectory_zero :
    dottieShiftedTrajectory 0 = ![0, 0, 0] := by
  unfold dottieShiftedTrajectory
  rw [dottieScalarSol_zero, Real.cos_zero, Real.sin_zero]
  simp

@[simp] lemma dottieShiftedTrajectory_apply0 (t : ℝ) :
    dottieShiftedTrajectory t 0 = dottieScalarSol t := rfl

@[simp] lemma dottieShiftedTrajectory_apply1 (t : ℝ) :
    dottieShiftedTrajectory t 1 = Real.cos (dottieScalarSol t) - 1 := rfl

@[simp] lemma dottieShiftedTrajectory_apply2 (t : ℝ) :
    dottieShiftedTrajectory t 2 = Real.sin (dottieScalarSol t) := rfl

/-! ## Syntactic field evaluation -/

/-- Direct evaluation of the shifted field at a real state. -/
theorem dottieShiftedPolyPIVP_evalField_eq (x : Fin 3 → ℝ) (i : Fin 3) :
    dottieShiftedPolyPIVP.toPIVP.field x i =
      (match i with
        | (0 : Fin 3) => x 1 - x 0 + 1
        | (1 : Fin 3) => x 2 * x 0 - x 2 * x 1 - x 2
        | (2 : Fin 3) => x 1 * x 1 + 2 * x 1 + 1 - x 0 * x 1 - x 0) := by
  show dottieShiftedPolyPIVP.evalField x i = _
  unfold PolyPIVP.evalField
  fin_cases i
  · show ((X 1 - X 0 + C 1 : MvPolynomial (Fin 3) ℚ)).eval₂ (Rat.castHom ℝ) x
      = x 1 - x 0 + 1
    simp [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_add, MvPolynomial.eval₂_X,
      MvPolynomial.eval₂_C]
  · show ((X 2 * X 0 - X 2 * X 1 - X 2 : MvPolynomial (Fin 3) ℚ)).eval₂
        (Rat.castHom ℝ) x = x 2 * x 0 - x 2 * x 1 - x 2
    simp [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
  · show ((X 1 * X 1 + C 2 * X 1 + C 1 - X 0 * X 1 - X 0 : MvPolynomial (Fin 3) ℚ)).eval₂
        (Rat.castHom ℝ) x = x 1 * x 1 + 2 * x 1 + 1 - x 0 * x 1 - x 0
    simp [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_X, MvPolynomial.eval₂_C]

/-! ## The shifted trajectory satisfies the shifted ODE -/

/-- For every `t ≥ 0`, `dottieShiftedTrajectory` satisfies the shifted PIVP's
field equation. Derived from `dottieTrajectory_hasDerivAt` using the chain
rule on `cos(x(t))` and `sin(x(t))`. -/
lemma dottieShiftedTrajectory_hasDerivAt (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt dottieShiftedTrajectory
      (dottieShiftedPolyPIVP.toPIVP.field (dottieShiftedTrajectory t)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  set x := dottieScalarSol t with hx_def
  have hx_deriv := dottieScalarSol_hasDerivAt t ht
  -- All three shifted-field values at the current state.
  -- Coordinate 0: u₁ − u₀ + 1 = (cos x − 1) − x + 1 = cos x − x = x'. ✓
  -- Coordinate 1: u₂·u₀ − u₂·u₁ − u₂
  --               = sin x · x − sin x · (cos x − 1) − sin x
  --               = sin x · x − sin x · cos x + sin x − sin x
  --               = sin x · x − sin x · cos x
  --               = −sin x · (cos x − x) = d/dt (cos x − 1). ✓
  -- Coordinate 2: u₁² + 2·u₁ + 1 − u₀·u₁ − u₀
  --               = (cos x − 1)² + 2·(cos x − 1) + 1 − x·(cos x − 1) − x
  --               = cos²x − 2·cos x + 1 + 2·cos x − 2 + 1 − x·cos x + x − x
  --               = cos²x − x·cos x
  --               = cos x · (cos x − x) = d/dt (sin x). ✓
  fin_cases i
  · -- i = 0: u₀' = cos(x) − x.
    show HasDerivAt (fun s => dottieShiftedTrajectory s 0)
      (dottieShiftedPolyPIVP.toPIVP.field (dottieShiftedTrajectory t) 0) t
    have hfield : dottieShiftedPolyPIVP.toPIVP.field (dottieShiftedTrajectory t) 0
        = Real.cos x - x := by
      rw [dottieShiftedPolyPIVP_evalField_eq]
      show dottieShiftedTrajectory t 1 - dottieShiftedTrajectory t 0 + 1
        = Real.cos x - x
      rw [dottieShiftedTrajectory_apply0, dottieShiftedTrajectory_apply1]
      show Real.cos x - 1 - x + 1 = Real.cos x - x
      ring
    rw [hfield]
    have hfun : (fun s => dottieShiftedTrajectory s 0) = dottieScalarSol := by
      funext s; rfl
    rw [hfun]
    exact hx_deriv
  · -- i = 1: u₁' = −sin(x) · (cos x − x).
    show HasDerivAt (fun s => dottieShiftedTrajectory s 1)
      (dottieShiftedPolyPIVP.toPIVP.field (dottieShiftedTrajectory t) 1) t
    have hfield : dottieShiftedPolyPIVP.toPIVP.field (dottieShiftedTrajectory t) 1
        = -Real.sin x * (Real.cos x - x) := by
      rw [dottieShiftedPolyPIVP_evalField_eq]
      show dottieShiftedTrajectory t 2 * dottieShiftedTrajectory t 0
        - dottieShiftedTrajectory t 2 * dottieShiftedTrajectory t 1
        - dottieShiftedTrajectory t 2
        = -Real.sin x * (Real.cos x - x)
      rw [dottieShiftedTrajectory_apply0, dottieShiftedTrajectory_apply1,
        dottieShiftedTrajectory_apply2]
      ring
    rw [hfield]
    have hfun : (fun s => dottieShiftedTrajectory s 1)
        = (fun s => Real.cos (dottieScalarSol s) - 1) := by
      funext s; rfl
    rw [hfun]
    have hcos : HasDerivAt Real.cos (-Real.sin x) x := Real.hasDerivAt_cos x
    have hcomp : HasDerivAt (fun s => Real.cos (dottieScalarSol s))
        (-Real.sin x * (Real.cos x - x)) t := hcos.comp t hx_deriv
    have := hcomp.sub_const (1 : ℝ)
    exact this
  · -- i = 2: u₂' = cos(x) · (cos x − x).
    show HasDerivAt (fun s => dottieShiftedTrajectory s 2)
      (dottieShiftedPolyPIVP.toPIVP.field (dottieShiftedTrajectory t) 2) t
    have hfield : dottieShiftedPolyPIVP.toPIVP.field (dottieShiftedTrajectory t) 2
        = Real.cos x * (Real.cos x - x) := by
      rw [dottieShiftedPolyPIVP_evalField_eq]
      show dottieShiftedTrajectory t 1 * dottieShiftedTrajectory t 1
          + 2 * dottieShiftedTrajectory t 1 + 1
          - dottieShiftedTrajectory t 0 * dottieShiftedTrajectory t 1
          - dottieShiftedTrajectory t 0
        = Real.cos x * (Real.cos x - x)
      rw [dottieShiftedTrajectory_apply0, dottieShiftedTrajectory_apply1]
      ring
    rw [hfield]
    have hfun : (fun s => dottieShiftedTrajectory s 2)
        = (fun s => Real.sin (dottieScalarSol s)) := by
      funext s; rfl
    rw [hfun]
    have hsin : HasDerivAt Real.sin (Real.cos x) x := Real.hasDerivAt_sin x
    exact hsin.comp t hx_deriv

/-- Initial condition matches. -/
lemma dottieShiftedTrajectory_init :
    dottieShiftedTrajectory 0 = dottieShiftedPolyPIVP.toPIVP.init := by
  rw [dottieShiftedTrajectory_zero]
  ext i
  fin_cases i <;> simp [dottieShiftedPolyPIVP, PolyPIVP.toPIVP]

/-- The `PIVP.Solution` bundle for the shifted PIVP. -/
noncomputable def dottieShiftedSolution :
    Ripple.PIVP.Solution dottieShiftedPolyPIVP.toPIVP where
  trajectory := dottieShiftedTrajectory
  init_cond := dottieShiftedTrajectory_init
  is_solution := dottieShiftedTrajectory_hasDerivAt

/-! ## Boundedness of the shifted trajectory -/

lemma dottieShiftedTrajectory_bounded :
    dottieShiftedPolyPIVP.toPIVP.IsBounded dottieShiftedTrajectory := by
  refine ⟨3, by norm_num, ?_⟩
  intro t ht
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 3)]
  intro i
  unfold dottieShiftedTrajectory
  fin_cases i
  · -- |x(t)| ≤ dottieNumber ≤ 1 ≤ 3
    simp [Real.norm_eq_abs]
    have hbounds := dottieScalarSol_bounds t ht
    rw [abs_of_nonneg hbounds.1]
    linarith [dottieNumber_le_one]
  · -- |cos(x) - 1| ≤ 2 ≤ 3  (since -1 ≤ cos ≤ 1 ⇒ -2 ≤ cos - 1 ≤ 0)
    simp [Real.norm_eq_abs]
    have h_upper : Real.cos (dottieScalarSol t) ≤ 1 := Real.cos_le_one _
    have h_lower : -1 ≤ Real.cos (dottieScalarSol t) := Real.neg_one_le_cos _
    have h_abs : |Real.cos (dottieScalarSol t) - 1| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith
    linarith
  · -- |sin(x)| ≤ 1 ≤ 3
    simp [Real.norm_eq_abs]
    have : |Real.sin (dottieScalarSol t)| ≤ 1 := Real.abs_sin_le_one _
    linarith

/-! ## `BoundedTimeComputable` for the shifted PIVP -/

/-- The `BoundedTimeComputable` bundle for the shifted Dottie PIVP. -/
noncomputable def dottieShiftedBTC :
    Ripple.BoundedTimeComputable 3 dottieNumber where
  pivp := dottieShiftedPolyPIVP.toPIVP
  sol := dottieShiftedSolution
  modulus := fun r => (r : ℝ) + 1
  bounded := dottieShiftedTrajectory_bounded
  convergence := by
    intro r t ht
    -- Output coordinate is 0 = the scalar solution; same convergence as `dottieBTC`.
    show |dottieShiftedSolution.trajectory t dottieShiftedPolyPIVP.toPIVP.output
          - dottieNumber| < Real.exp (-(r : ℝ))
    have hout : dottieShiftedPolyPIVP.toPIVP.output = (0 : Fin 3) := rfl
    rw [hout]
    have hcoord : dottieShiftedSolution.trajectory t 0 = dottieScalarSol t := rfl
    rw [hcoord]
    have ht_nn : 0 ≤ t := by
      have h1 : (0 : ℝ) ≤ (r : ℝ) + 1 := by positivity
      linarith
    have hconv : |dottieScalarSol t - dottieNumber| ≤ dottieNumber * Real.exp (-t) :=
      dottieScalarSol_convergence t ht_nn
    have h1 : dottieNumber * Real.exp (-t) < 1 * Real.exp (-t) := by
      apply mul_lt_mul_of_pos_right dottieNumber_lt_one (Real.exp_pos _)
    have h2 : Real.exp (-t) < Real.exp (-(r : ℝ)) := by
      apply Real.exp_lt_exp.mpr
      linarith
    have h3 : 1 * Real.exp (-t) = Real.exp (-t) := by ring
    linarith

/-! ## Stage 3: Tier 1 composition → CBTC + PCD -/

/-- Shifted polynomial field (as a function `Fin 3 → MvPolynomial (Fin 3) ℚ`)
for use with the Tier 1 composition. -/
noncomputable def dottieShiftedFieldPoly : Fin 3 → MvPolynomial (Fin 3) ℚ :=
  fun i =>
    match i with
    | ⟨0, _⟩ => X 1 - X 0 + C 1
    | ⟨1, _⟩ => X 2 * X 0 - X 2 * X 1 - X 2
    | ⟨2, _⟩ => X 1 * X 1 + C 2 * X 1 + C 1 - X 0 * X 1 - X 0
    | ⟨n+3, hn⟩ => absurd hn (by omega)

/-- `dottieShiftedBTC.pivp.field` is the evaluation of `dottieShiftedFieldPoly`. -/
lemma dottieShiftedBTC_h_field (y : Fin 3 → ℝ) (i : Fin 3) :
    dottieShiftedBTC.pivp.field y i
      = (dottieShiftedFieldPoly i).eval₂ (Rat.castHom ℝ) y := by
  show dottieShiftedPolyPIVP.toPIVP.field y i = _
  show dottieShiftedPolyPIVP.evalField y i = _
  unfold PolyPIVP.evalField dottieShiftedPolyPIVP dottieShiftedFieldPoly
  fin_cases i <;> rfl

/-- The shifted PIVP has zero initial conditions. -/
lemma dottieShiftedBTC_h_zero : ∀ j, dottieShiftedBTC.pivp.init j = 0 := by
  intro j
  show (dottieShiftedPolyPIVP.toPIVP.init j : ℝ) = 0
  show ((dottieShiftedPolyPIVP.init j : ℚ) : ℝ) = 0
  fin_cases j <;> simp [dottieShiftedPolyPIVP]

/-- Stage 3 result: a CBTC + PCD for `dottieNumber`. -/
lemma dottie_cbtc_pcd :
    ∃ (d' : ℕ) (cbtc' : CertifiedBoundedTimeComputable d' dottieNumber)
      (_ : PolyCRNDecomposition d' cbtc'.pivp), True :=
  Ripple.DualRail.btc_to_cbtc_pcd_of_unit_interval
    dottieShiftedBTC dottieShiftedFieldPoly
    dottieShiftedBTC_h_field dottieShiftedBTC_h_zero
    dottieNumber_nonneg dottieNumber_le_one

/-- Existence wrapper for `IsLPPComputable dottieNumber` at the `Prop` level.
`IsLPPComputable` is a `Type` (a structure), so the `Prop`-valued existential
`∃ _ : IsLPPComputable dottieNumber, True` provided by
`bounded_crn_is_lpp_computable_unconditional` cannot be `obtain`-ed directly
into a `Type`-valued term without going through `Classical.choice`. -/
lemma exists_dottie_lpp : ∃ _ : IsLPPComputable dottieNumber, True := by
  obtain ⟨d', cbtc', pcd', _⟩ := dottie_cbtc_pcd
  have hα01 : 0 ≤ dottieNumber ∧ dottieNumber ≤ 1 :=
    ⟨dottieNumber_nonneg, dottieNumber_le_one⟩
  exact Ripple.bounded_crn_is_lpp_computable_unconditional hα01 cbtc' pcd'

/-! ## Stage 4: CBTC + PCD → IsLPPComputable -/

/-- **The Dottie number is LPP-computable.**

Pipeline:
  (1) `dottieBTC` from `Ripple.Number.Dottie` (Stage 1).
  (2) `dottieShiftedBTC` (Stage 2) — init shift `u₁ := Y − 1` so that all
      initial conditions vanish.
  (3) `Tier1Composition.btc_to_cbtc_pcd_of_unit_interval` (Stage 3) — compile
      the shifted zero-init BTC into a `CertifiedBoundedTimeComputable +
      PolyCRNDecomposition` witness via the polynomial-scale dual-rail plus
      Lemma 8 subtraction.
  (4) `bounded_crn_is_lpp_computable_unconditional` (Stage 4) — lift to
      `IsLPPComputable`. -/
noncomputable def dottieNumber_isLPPComputable : IsLPPComputable dottieNumber :=
  Classical.choice (let ⟨lpp, _⟩ := exists_dottie_lpp; ⟨lpp⟩)

end Ripple.Number
