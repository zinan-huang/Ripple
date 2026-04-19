/-
  Ripple.LPP.SaturatingSurrogate — Saturating low-pass filter patch for LPP.

  The DNA28 LPP paper's Stage 2 slack requires `x_out(σ) ≤ M_out < 1` pointwise
  for σ ≥ 0. Generic CBTCs only provide `‖sol t‖ ≤ M` with potentially `M > 1`;
  even the output coordinate can transiently exceed `1`.

  **Construction (see `projects/Bounded/notes/saturating-surrogate-LPP.tex`).**
  Pick any rational `U` with `α < U < 1`. Append a tracker species `y` with
    `y' = (x - y)(U - y) = U·x + y² − (x + U)·y`
    `y(0) = 0`.
  The factor `(U - y)` is a hard cap: at `y = U`, `y' = 0` irrespective of `x`,
  so `y(t) ∈ [0, U]` for all `t ≥ 0`. Time-rescaling by
    τ(t) := ∫₀ᵗ (U - y(s)) ds
  converts the nonlinear ODE to `Φ'(τ) = (x∘t)(τ) − Φ(τ)` whose Duhamel solution
  gives `y(t) → α` with an explicit modulus.

  **Non-negativity of coefficients** is preserved: production is `U·X_out + X_y²`,
  degradation is `X_out + U`, both with `≥ 0` rational coefficients (since
  `0 ≤ U` and `X_out ≥ 0`, `X_y ≥ 0` in the semantic solution).

  The structural extension (polynomial algebra, `Fin.snoc`, PCD lifting) is
  proved here. The analytic content — existence of the solution, the
  invariance `y ∈ [0, U]`, and convergence `y → α` with a computable modulus —
  is stated as a narrow residual witness `saturating_tracker_solution`,
  analogous to `relaxation_tracker_solution` in `AddRationalPos.lean`.
-/

import Ripple.Core.BoundedTime
import Ripple.LPP.Defs
import Mathlib.Algebra.MvPolynomial.Rename

namespace Ripple
namespace Saturating

open MvPolynomial

/-! ## Step 1: lift a `PolyPIVP d` to `PolyPIVP (d+1)` via `Fin.castSucc`.

Identical pattern to `Ripple.Algebraic.liftField/liftProd/liftDegr`. -/

/-- Rename the field polynomials along `Fin.castSucc`. -/
noncomputable def liftField {d : ℕ} (P : PolyPIVP d) :
    Fin d → MvPolynomial (Fin (d+1)) ℚ :=
  fun i => rename Fin.castSucc (P.field i)

/-- Rename production polynomials along `Fin.castSucc`. -/
noncomputable def liftProd {d : ℕ} {P : PolyPIVP d}
    (pcd : PolyCRNDecomposition d P) :
    Fin d → MvPolynomial (Fin (d+1)) ℚ :=
  fun i => rename Fin.castSucc (pcd.prod i)

/-- Rename degradation polynomials along `Fin.castSucc`. -/
noncomputable def liftDegr {d : ℕ} {P : PolyPIVP d}
    (pcd : PolyCRNDecomposition d P) :
    Fin d → MvPolynomial (Fin (d+1)) ℚ :=
  fun i => rename Fin.castSucc (pcd.degr i)

/-- Non-negativity of coefficients is preserved by `rename` along injections. -/
lemma coeff_rename_castSucc_nonneg {d : ℕ} (p : MvPolynomial (Fin d) ℚ)
    (hp : ∀ σ, 0 ≤ p.coeff σ) :
    ∀ σ, 0 ≤ (rename (Fin.castSucc (n := d)) p).coeff σ := by
  classical
  intro σ
  by_cases h : ∃ u : Fin d →₀ ℕ, u.mapDomain Fin.castSucc = σ
  · obtain ⟨u, hu⟩ := h
    subst hu
    rw [coeff_rename_mapDomain Fin.castSucc (Fin.castSucc_injective d)]
    exact hp u
  · rw [coeff_rename_eq_zero Fin.castSucc p σ (by
      intro u hu; exact absurd ⟨u, hu⟩ h)]

/-! ## Step 2: the saturating tracker field for the new species `y`.

  y' = (x - y)(U - y) = U·x + y² − (x + U)·y
  prod_y = U·X_out + X_y²
  degr_y = X_out + U
  degr_y · X_y = X_out · X_y + U · X_y
  prod_y − degr_y · X_y = U·X_out + X_y² − X_out·X_y − U·X_y
                        = (X_out − X_y)(U − X_y)
-/

/-- Production polynomial for the tracker: `prod_y = U · X_out + X_y²`. -/
noncomputable def saturatingProd {d : ℕ} (P : PolyPIVP d) (U : ℚ) :
    MvPolynomial (Fin (d+1)) ℚ :=
  C U * X (Fin.castSucc P.output) + X (Fin.last d) * X (Fin.last d)

/-- Degradation polynomial for the tracker: `degr_y = X_out + U`. -/
noncomputable def saturatingDegr {d : ℕ} (P : PolyPIVP d) (U : ℚ) :
    MvPolynomial (Fin (d+1)) ℚ :=
  X (Fin.castSucc P.output) + C U

/-- Field polynomial for the tracker: `y' = prod_y − degr_y · X_y`. -/
noncomputable def saturatingField {d : ℕ} (P : PolyPIVP d) (U : ℚ) :
    MvPolynomial (Fin (d+1)) ℚ :=
  saturatingProd P U - saturatingDegr P U * X (Fin.last d)

lemma saturatingProd_coeff_nonneg {d : ℕ} (P : PolyPIVP d) (U : ℚ) (hU : 0 ≤ U) :
    ∀ σ, 0 ≤ (saturatingProd P U).coeff σ := by
  classical
  intro σ
  unfold saturatingProd
  rw [MvPolynomial.coeff_add]
  have h1 : 0 ≤ (C U * X (Fin.castSucc P.output) :
      MvPolynomial (Fin (d+1)) ℚ).coeff σ := by
    rw [coeff_C_mul, MvPolynomial.coeff_X']
    split_ifs
    · simp [hU]
    · simp
  have h2 : 0 ≤ (X (Fin.last d) * X (Fin.last d) :
      MvPolynomial (Fin (d+1)) ℚ).coeff σ := by
    rw [MvPolynomial.coeff_mul]
    apply Finset.sum_nonneg
    intro p _
    rw [MvPolynomial.coeff_X', MvPolynomial.coeff_X']
    split_ifs <;> norm_num
  linarith

lemma saturatingDegr_coeff_nonneg {d : ℕ} (P : PolyPIVP d) (U : ℚ) (hU : 0 ≤ U) :
    ∀ σ, 0 ≤ (saturatingDegr P U).coeff σ := by
  classical
  intro σ
  unfold saturatingDegr
  rw [MvPolynomial.coeff_add]
  have h1 : 0 ≤ (X (Fin.castSucc P.output) :
      MvPolynomial (Fin (d+1)) ℚ).coeff σ := by
    rw [MvPolynomial.coeff_X']
    split_ifs <;> norm_num
  have h2 : 0 ≤ (C U : MvPolynomial (Fin (d+1)) ℚ).coeff σ := by
    rw [MvPolynomial.coeff_C]
    split_ifs
    · exact hU
    · exact le_refl _
  linarith

/-! ## Step 3: build the extended `PolyPIVP (d+1)` via `Fin.snoc`. -/

/-- The extended saturating-tracker PIVP. -/
noncomputable def saturatingPIVP {d : ℕ} (P : PolyPIVP d) (U : ℚ) :
    PolyPIVP (d+1) where
  field := Fin.snoc (liftField P) (saturatingField P U)
  init := Fin.snoc (fun i => P.init i) 0
  output := Fin.last d

@[simp] lemma saturatingPIVP_output {d : ℕ} (P : PolyPIVP d) (U : ℚ) :
    (saturatingPIVP P U).output = Fin.last d := rfl

@[simp] lemma saturatingPIVP_field_castSucc {d : ℕ} (P : PolyPIVP d) (U : ℚ)
    (i : Fin d) :
    (saturatingPIVP P U).field i.castSucc = rename Fin.castSucc (P.field i) := by
  unfold saturatingPIVP; simp [liftField, Fin.snoc_castSucc]

@[simp] lemma saturatingPIVP_field_last {d : ℕ} (P : PolyPIVP d) (U : ℚ) :
    (saturatingPIVP P U).field (Fin.last d) = saturatingField P U := by
  unfold saturatingPIVP; simp [Fin.snoc_last]

@[simp] lemma saturatingPIVP_init_castSucc {d : ℕ} (P : PolyPIVP d) (U : ℚ)
    (i : Fin d) :
    (saturatingPIVP P U).init i.castSucc = P.init i := by
  unfold saturatingPIVP; simp [Fin.snoc_castSucc]

@[simp] lemma saturatingPIVP_init_last {d : ℕ} (P : PolyPIVP d) (U : ℚ) :
    (saturatingPIVP P U).init (Fin.last d) = 0 := by
  unfold saturatingPIVP; simp [Fin.snoc_last]

/-! ## Step 4: `PolyCRNDecomposition` for the extended system. -/

/-- The extended system admits a `PolyCRNDecomposition` when the original does
and `0 ≤ U`. Tracker rows have non-negative coefficients by construction;
the original block inherits non-negativity through `rename Fin.castSucc`. -/
noncomputable def saturatingPIVP_polyCRN {d : ℕ} {P : PolyPIVP d} (U : ℚ)
    (hU : 0 ≤ U) (pcd : PolyCRNDecomposition d P) :
    PolyCRNDecomposition (d+1) (saturatingPIVP P U) where
  prod := Fin.snoc (liftProd pcd) (saturatingProd P U)
  degr := Fin.snoc (liftDegr pcd) (saturatingDegr P U)
  prod_nonneg := by
    intro i σ
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · rw [Fin.snoc_last]
      exact saturatingProd_coeff_nonneg P U hU σ
    · rw [Fin.snoc_castSucc]
      exact coeff_rename_castSucc_nonneg (pcd.prod i') (pcd.prod_nonneg i') σ
  degr_nonneg := by
    intro i σ
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · rw [Fin.snoc_last]
      exact saturatingDegr_coeff_nonneg P U hU σ
    · rw [Fin.snoc_castSucc]
      exact coeff_rename_castSucc_nonneg (pcd.degr i') (pcd.degr_nonneg i') σ
  init_nonneg := by
    intro i
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · simp
    · rw [saturatingPIVP_init_castSucc]; exact_mod_cast pcd.init_nonneg i'
  field_eq := by
    intro i
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · rw [saturatingPIVP_field_last, Fin.snoc_last, Fin.snoc_last]; rfl
    · rw [saturatingPIVP_field_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
      unfold liftProd liftDegr
      rw [pcd.field_eq i', map_sub, map_mul, rename_X]

/-! ## Step 5: analytic residual — existence of the saturating tracker solution.

Given a CBTC for `α` and any `U ∈ (α, 1) ∩ ℚ`, the extended system
`saturatingPIVP` has a solution on `[0, ∞)` extending the original trajectory
on the first `d` coordinates, with `y(t) ∈ [0, U]` and `y(t) → α` at an
explicit rate. This is the analytic content Mathlib does not give directly;
the paper-level argument is in `notes/saturating-surrogate-LPP.tex`.

Packaging as a single existential mirrors `relaxation_tracker_solution` in
`AddRationalPos.lean`. -/

/-- Residual witness: the extended PIVP has a certified bounded-time
computation for `α` (the same target), whose output trajectory stays
in `[0, U]` on `t ≥ 0`. Analytic content deferred. -/
axiom saturating_tracker_solution {d : ℕ} {α : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d α)
    (U : ℚ) (hα_nn : 0 ≤ α) (hU_lo : α < (U : ℝ)) (hU_hi : (U : ℝ) < 1) :
    ∃ (sol' : PIVP.Solution (saturatingPIVP cbtc.pivp U).toPIVP)
      (μ' : TimeModulus),
      -- Convergence at rate μ'.
      (∀ r : ℕ, ∀ t : ℝ, t > μ' r →
        |sol'.trajectory t (saturatingPIVP cbtc.pivp U).output - α|
          < Real.exp (-(r : ℝ))) ∧
      -- Boundedness of the whole vector trajectory.
      (saturatingPIVP cbtc.pivp U).toPIVP.IsBounded sol'.trajectory ∧
      -- Output stays in `[0, U]` on `t ≥ 0`.
      (∀ σ, 0 ≤ σ →
        0 ≤ sol'.trajectory σ (saturatingPIVP cbtc.pivp U).output ∧
        sol'.trajectory σ (saturatingPIVP cbtc.pivp U).output ≤ (U : ℝ))

/-! ## Step 6: package into a new CBTC + PCD with `output ≤ U` sharp bound.

This is the interface consumed by `BoundedLPP.lean`: given a generic CBTC+PCD
for `α ∈ [0, 1)`, produce a (higher-dimensional) CBTC+PCD for the same `α`
whose output trajectory is pointwise `≤ U` for some rational `α < U < 1`.
`U` is packaged existentially so the caller need not mention it. -/

theorem saturating_surrogate_cbtc {d : ℕ} {α : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d α)
    (pcd : PolyCRNDecomposition d cbtc.pivp)
    (hα_nn : 0 ≤ α) (hα_lt : α < 1) :
    ∃ (d' : ℕ) (cbtc' : CertifiedBoundedTimeComputable d' α)
      (_ : PolyCRNDecomposition d' cbtc'.pivp) (M_out : ℝ),
      α ≤ M_out ∧ M_out < 1 ∧
      (∀ σ, 0 ≤ σ → cbtc'.sol.trajectory σ cbtc'.pivp.output ≤ M_out) := by
  -- Pick a rational U strictly between α and 1.
  obtain ⟨qU, hαU, hU1⟩ := exists_rat_btwn hα_lt
  set U : ℚ := qU with hU_def
  have hU_lo : α < (U : ℝ) := hαU
  have hU_hi : (U : ℝ) < 1 := hU1
  have hU_nn : (0 : ℚ) ≤ U := by
    have : (0 : ℝ) ≤ (U : ℝ) := le_trans hα_nn hU_lo.le
    exact_mod_cast this
  -- Get the analytic witness.
  obtain ⟨sol', μ', hconv, hbdd, hrange⟩ :=
    saturating_tracker_solution cbtc U hα_nn hU_lo hU_hi
  refine ⟨d + 1,
    { pivp := saturatingPIVP cbtc.pivp U
      sol := sol'
      modulus := μ'
      bounded := hbdd
      convergence := hconv },
    saturatingPIVP_polyCRN U hU_nn pcd,
    (U : ℝ), hU_lo.le, hU_hi, ?_⟩
  intro σ hσ
  exact (hrange σ hσ).2

end Saturating
end Ripple
