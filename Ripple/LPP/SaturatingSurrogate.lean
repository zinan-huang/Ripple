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
import Ripple.Core.ZeroInitPositivity
import Ripple.LPP.Defs
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Analysis.ODE.Gronwall

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

/-! ## Step 4b: evaluation of the extended field.

Decomposes `(saturatingPIVP P U).toPIVP.field` on the two coordinate classes,
reducing the extended vector field to the original one (on `castSucc` rows)
and to the scalar saturating-tracker expression (on the last row). These are
the structural glue used to verify that the eventual explicit trajectory
satisfies the extended ODE. -/

/-- Evaluation on a `castSucc` coordinate reduces to the original field
evaluated on the restricted state vector. -/
lemma evalField_castSucc {d : ℕ} (P : PolyPIVP d) (U : ℚ)
    (x : Fin (d+1) → ℝ) (i : Fin d) :
    (saturatingPIVP P U).toPIVP.field x i.castSucc
      = P.toPIVP.field (fun j : Fin d => x j.castSucc) i := by
  show ((saturatingPIVP P U).field i.castSucc).eval₂ (Rat.castHom ℝ) x
      = (P.field i).eval₂ (Rat.castHom ℝ) (fun j : Fin d => x j.castSucc)
  rw [saturatingPIVP_field_castSucc]
  exact eval₂_rename (Rat.castHom ℝ) Fin.castSucc x (P.field i)

/-- Evaluation on the last coordinate gives the scalar saturating-tracker
expression `(x_out − x_y)(U − x_y)`. -/
lemma evalField_last {d : ℕ} (P : PolyPIVP d) (U : ℚ)
    (x : Fin (d+1) → ℝ) :
    (saturatingPIVP P U).toPIVP.field x (Fin.last d)
      = (x P.output.castSucc - x (Fin.last d)) *
          ((U : ℝ) - x (Fin.last d)) := by
  show ((saturatingPIVP P U).field (Fin.last d)).eval₂ (Rat.castHom ℝ) x
      = _
  rw [saturatingPIVP_field_last]
  unfold saturatingField saturatingProd saturatingDegr
  simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_C, eval₂_X]
  show (Rat.castHom ℝ) U * x P.output.castSucc + x (Fin.last d) * x (Fin.last d) -
        (x P.output.castSucc + (Rat.castHom ℝ) U) * x (Fin.last d)
      = (x P.output.castSucc - x (Fin.last d)) * ((Rat.castHom ℝ) U - x (Fin.last d))
  ring

/-- **Phase B1 (Lipschitz).** The extended vector field is locally Lipschitz
in the state variable — immediate from the polynomial-field locally-Lipschitz
theorem applied to the extended `PolyPIVP`. This is the first ingredient for
invoking `locally_lipschitz_bounded_global_ode_proved` on the extended system. -/
theorem saturatingPIVP_field_locally_lipschitz {d : ℕ} (P : PolyPIVP d) (U : ℚ) :
    ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin (d + 1) → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖(saturatingPIVP P U).toPIVP.field x - (saturatingPIVP P U).toPIVP.field y‖
        ≤ L * ‖x - y‖ :=
  polyPIVP_field_locally_lipschitz (saturatingPIVP P U)

/-! ## Phase B3: scalar barrier invariance.

Given `y : ℝ → ℝ` satisfying `y(0) = 0` and
`y'(t) = (x(t) − y(t))(U − y(t))` on `[0, T)` with `x ≥ 0` and `U > 0`,
we prove `0 ≤ y(t) ≤ U` on `[0, T)`.

The lower bound uses MVT: if `y(t₀) < 0`, let `s` be the supremum of
`{u ∈ [0, t₀] : 0 ≤ y(u)}`. Continuity gives `y(s) = 0`. On `(s, t₀]`
we have `y(u) < 0 < U` and `x(u) ≥ 0`, so `y'(u) = (x(u) − y(u))(U − y(u)) > 0`.
Mean-value theorem on `[s, t₀]` gives `y(t₀) > y(s) = 0`, contradicting
`y(t₀) < 0`.

The upper bound uses ODE uniqueness: at the first crossing `s` with
`y(s) = U`, both `y` and the constant `U` solve the tracker ODE with the
same initial value at `s`. Uniqueness forces `y ≡ U` on `[s, t₀]`, but
`y(t₀) > U` by hypothesis.
-/

/-- Lower scalar barrier for the saturating tracker. -/
lemma saturating_barrier_lower {T U : ℝ}
    {x y : ℝ → ℝ}
    (hU_pos : 0 < U)
    (hx_nn : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ x t)
    (hy0 : y 0 = 0)
    (hy_deriv : ∀ t, 0 ≤ t → t < T →
      HasDerivAt y ((x t - y t) * (U - y t)) t) :
    ∀ t, 0 ≤ t → t < T → 0 ≤ y t := by
  intro t ht_nn ht_lt
  by_contra h_neg
  push_neg at h_neg
  -- h_neg : y t < 0.  y is continuous on [0, t] from HasDerivAt.
  have hy_cont : ContinuousOn y (Set.Icc 0 t) := by
    intro u hu
    have hu_lt : u < T := lt_of_le_of_lt hu.2 ht_lt
    exact (hy_deriv u hu.1 hu_lt).continuousAt.continuousWithinAt
  -- S := {u ∈ [0, t] | 0 ≤ y u}, contains 0, bounded above by t.
  let S : Set ℝ := {u | u ∈ Set.Icc (0 : ℝ) t ∧ 0 ≤ y u}
  have h0_mem : (0 : ℝ) ∈ S := ⟨⟨le_refl _, ht_nn⟩, by rw [hy0]⟩
  have hS_bdd : BddAbove S := ⟨t, fun u hu => hu.1.2⟩
  have hS_nonempty : S.Nonempty := ⟨0, h0_mem⟩
  set s := sSup S with hs_def
  have hs_le_t : s ≤ t := csSup_le hS_nonempty (fun u hu => hu.1.2)
  have hs_nn : 0 ≤ s := le_csSup hS_bdd h0_mem
  have hs_in_Icc : s ∈ Set.Icc (0 : ℝ) t := ⟨hs_nn, hs_le_t⟩
  -- 0 ≤ y s: take a sequence uₙ ∈ S with uₙ → s, use continuity of y at s.
  have hys_nn : 0 ≤ y s := by
    have hy_cont_s : ContinuousWithinAt y (Set.Icc 0 t) s :=
      hy_cont s hs_in_Icc
    -- Build a sequence in S converging to s.
    rcases eq_or_lt_of_le hs_nn with hs_zero | hs_pos
    · -- s = 0, so y s = y 0 = 0.
      rw [← hs_zero, hy0]
    · -- s > 0, construct sequence uₙ = s - min(s, 1/(n+1))
      have h_seq : ∀ ε > 0, ∃ u ∈ S, s - ε < u ∧ u ≤ s := by
        intro ε hε
        obtain ⟨u, hu_mem, hu_lt⟩ :=
          exists_lt_of_lt_csSup hS_nonempty (show s - ε < s by linarith)
        exact ⟨u, hu_mem, hu_lt, le_csSup hS_bdd hu_mem⟩
      -- y s = lim y uₙ, and y uₙ ≥ 0, so y s ≥ 0.
      have : ∀ ε > 0, ∃ u ∈ Set.Icc (0:ℝ) t, |u - s| < ε ∧ 0 ≤ y u := by
        intro ε hε
        obtain ⟨u, ⟨hu1, hu2⟩, hu_lt, hu_le⟩ := h_seq ε hε
        refine ⟨u, hu1, ?_, hu2⟩
        rw [abs_sub_lt_iff]
        exact ⟨by linarith, by linarith⟩
      by_contra h_ys_neg
      push_neg at h_ys_neg
      rw [Metric.continuousWithinAt_iff] at hy_cont_s
      obtain ⟨δ, hδ, hδ_prop⟩ := hy_cont_s (-y s / 2) (by linarith)
      obtain ⟨u, hu_in, hu_dist, hyu_nn⟩ := this δ hδ
      have := hδ_prop hu_in (by rw [Real.dist_eq]; exact hu_dist)
      rw [Real.dist_eq] at this
      have := abs_sub_lt_iff.mp this
      linarith
  -- s < t: if s = t, then 0 ≤ y t but h_neg says y t < 0.
  have hs_lt_t : s < t := by
    rcases lt_or_eq_of_le hs_le_t with h | h
    · exact h
    · exfalso; rw [← h] at h_neg; linarith
  -- For u ∈ (s, t], u ∉ S, but u ∈ Icc 0 t, so y u < 0.
  have hy_neg_on : ∀ u, s < u → u ≤ t → y u < 0 := by
    intro u hsu hut
    by_contra hu_nn
    push_neg at hu_nn
    have hu_in_S : u ∈ S :=
      ⟨⟨le_trans hs_nn (le_of_lt hsu), hut⟩, hu_nn⟩
    have : u ≤ s := le_csSup hS_bdd hu_in_S
    linarith
  -- By continuity at s: y s = 0 (since y s ≥ 0 and limit of y u for u ↘ s is ≤ 0).
  have hys_zero : y s = 0 := by
    refine le_antisymm ?_ hys_nn
    -- y s ≤ 0 by taking limit from the right: y s = lim_{u → s+} y u ≤ 0.
    -- Sequence: uₙ = s + (t − s)/(n+1) ∈ (s, t], so y uₙ < 0.
    by_contra h_pos
    push_neg at h_pos
    -- y s > 0. Continuity gives a neighborhood where y > 0, but any such
    -- neighborhood hits (s, t] where y < 0. Contradiction.
    have hy_cont_s : ContinuousWithinAt y (Set.Icc 0 t) s :=
      hy_cont s hs_in_Icc
    rw [Metric.continuousWithinAt_iff] at hy_cont_s
    obtain ⟨δ, hδ, hδ_prop⟩ := hy_cont_s (y s) h_pos
    -- Pick u = min (s + δ/2) t, in (s, t].
    set u := min (s + δ / 2) t with hu_def
    have hu_lt_t : u ≤ t := min_le_right _ _
    have hsu : s < u := by
      have h1 : s < s + δ / 2 := by linarith
      have h2 : s < t := hs_lt_t
      exact lt_min h1 h2
    have hu_mem : u ∈ Set.Icc (0 : ℝ) t :=
      ⟨le_trans hs_nn (le_of_lt hsu), hu_lt_t⟩
    have h_dist : dist u s < δ := by
      have h1 : u ≤ s + δ / 2 := min_le_left _ _
      rw [Real.dist_eq, abs_of_pos (by linarith : (0:ℝ) < u - s)]
      linarith
    have h_apply := hδ_prop hu_mem h_dist
    have hyu_close : |y u - y s| < y s := by rwa [Real.dist_eq] at h_apply
    have hyu_neg : y u < 0 := hy_neg_on u hsu hu_lt_t
    have : y u > 0 := by
      have := abs_sub_lt_iff.mp hyu_close
      linarith
    linarith
  -- On (s, t], y' > 0 because y < 0 < U and x ≥ 0.
  have hy_deriv_pos : ∀ u, s < u → u < t →
      HasDerivAt y ((x u - y u) * (U - y u)) u ∧
      0 < (x u - y u) * (U - y u) := by
    intro u hsu hut
    have hu_nn : 0 ≤ u := le_trans hs_nn (le_of_lt hsu)
    have hu_lt_T : u < T := lt_trans hut ht_lt
    refine ⟨hy_deriv u hu_nn hu_lt_T, ?_⟩
    have hy_neg_u : y u < 0 := hy_neg_on u hsu (le_of_lt hut)
    have hx_nn_u : 0 ≤ x u :=
      hx_nn u hu_nn (le_of_lt hu_lt_T)
    have h1 : 0 < x u - y u := by linarith
    have h2 : 0 < U - y u := by linarith
    exact mul_pos h1 h2
  -- Apply MVT on [s, t]: ∃ ξ ∈ (s, t) with y t - y s = y'(ξ) * (t - s).
  have hy_cont_st : ContinuousOn y (Set.Icc s t) :=
    hy_cont.mono (fun u hu => ⟨le_trans hs_nn hu.1, hu.2⟩)
  have hy_diff_st : ∀ u ∈ Set.Ioo s t, HasDerivAt y
      ((x u - y u) * (U - y u)) u := by
    intro u ⟨hu1, hu2⟩
    exact (hy_deriv_pos u hu1 hu2).1
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ :=
    exists_hasDerivAt_eq_slope y (fun u => (x u - y u) * (U - y u))
      hs_lt_t hy_cont_st (fun u hu => hy_diff_st u hu)
  -- hξ_eq : (x ξ - y ξ) * (U - y ξ) = (y t - y s) / (t - s)
  have hξ_pos : 0 < (x ξ - y ξ) * (U - y ξ) :=
    (hy_deriv_pos ξ hξ_mem.1 hξ_mem.2).2
  have htsub : 0 < t - s := by linarith
  -- Therefore y t - y s > 0, so y t > 0.  But h_neg : y t < 0. Contradiction.
  rw [hys_zero, sub_zero] at hξ_eq
  have : 0 < y t / (t - s) := hξ_eq ▸ hξ_pos
  have : 0 < y t := by
    have := mul_pos this htsub
    rw [div_mul_cancel₀ _ (ne_of_gt htsub)] at this
    exact this
  linarith

/-- Upper scalar barrier for the saturating tracker. At first crossing `s`
with `y s = U`, both `y` and the constant function `c ≡ U` solve the
tracker ODE starting at `U`. Uniqueness forces `y ≡ U` on `[s, t]`,
contradicting `y t > U`. -/
lemma saturating_barrier_upper {T U : ℝ}
    {x y : ℝ → ℝ}
    (hU_pos : 0 < U)
    (hx_cont : ContinuousOn x (Set.Icc 0 T))
    (hy0 : y 0 = 0)
    (hy_deriv : ∀ t, 0 ≤ t → t < T →
      HasDerivAt y ((x t - y t) * (U - y t)) t) :
    ∀ t, 0 ≤ t → t < T → y t ≤ U := by
  intro t ht_nn ht_lt
  by_contra h_gt
  push_neg at h_gt
  -- h_gt : U < y t. y is continuous on [0, t].
  have hy_cont : ContinuousOn y (Set.Icc 0 t) := by
    intro u hu
    have hu_lt : u < T := lt_of_le_of_lt hu.2 ht_lt
    exact (hy_deriv u hu.1 hu_lt).continuousAt.continuousWithinAt
  -- S := {u ∈ [0, t] | y u ≤ U}, contains 0, bounded by t.
  let S : Set ℝ := {u | u ∈ Set.Icc (0 : ℝ) t ∧ y u ≤ U}
  have h0_mem : (0 : ℝ) ∈ S :=
    ⟨⟨le_refl _, ht_nn⟩, by rw [hy0]; exact hU_pos.le⟩
  have hS_bdd : BddAbove S := ⟨t, fun u hu => hu.1.2⟩
  have hS_nonempty : S.Nonempty := ⟨0, h0_mem⟩
  set s := sSup S with hs_def
  have hs_le_t : s ≤ t := csSup_le hS_nonempty (fun u hu => hu.1.2)
  have hs_nn : 0 ≤ s := le_csSup hS_bdd h0_mem
  have hs_in_Icc : s ∈ Set.Icc (0 : ℝ) t := ⟨hs_nn, hs_le_t⟩
  -- By continuity: y s ≤ U (limit of y uₙ ≤ U for uₙ ∈ S, uₙ → s).
  have hys_le : y s ≤ U := by
    rcases eq_or_lt_of_le hs_nn with hs_zero | hs_pos
    · rw [← hs_zero, hy0]; exact hU_pos.le
    · by_contra h_ys_gt
      push_neg at h_ys_gt
      have hy_cont_s : ContinuousWithinAt y (Set.Icc 0 t) s := hy_cont s hs_in_Icc
      rw [Metric.continuousWithinAt_iff] at hy_cont_s
      obtain ⟨δ, hδ, hδ_prop⟩ := hy_cont_s ((y s - U) / 2) (by linarith)
      obtain ⟨u, hu_mem, hu_lt⟩ :=
        exists_lt_of_lt_csSup hS_nonempty (show s - δ < s by linarith)
      have hu_le : u ≤ s := le_csSup hS_bdd hu_mem
      have hu_dist : |u - s| < δ := by
        rw [abs_sub_lt_iff]; exact ⟨by linarith, by linarith⟩
      have := hδ_prop hu_mem.1 (by rw [Real.dist_eq]; exact hu_dist)
      rw [Real.dist_eq] at this
      have := abs_sub_lt_iff.mp this
      linarith [hu_mem.2]
  -- s < t, else y t = y s ≤ U contradicts y t > U.
  have hs_lt_t : s < t := by
    rcases lt_or_eq_of_le hs_le_t with h | h
    · exact h
    · exfalso; rw [← h] at h_gt; linarith
  -- y s = U (y s ≤ U and y s ≥ U by continuity from above, where y > U).
  have hys_eq : y s = U := by
    refine le_antisymm hys_le ?_
    by_contra h_ys_lt
    push_neg at h_ys_lt
    -- y s < U. Continuity gives a right-neighborhood [s, s + δ) ⊂ S.
    have hy_cont_s : ContinuousWithinAt y (Set.Icc 0 t) s := hy_cont s hs_in_Icc
    rw [Metric.continuousWithinAt_iff] at hy_cont_s
    obtain ⟨δ, hδ, hδ_prop⟩ := hy_cont_s ((U - y s) / 2) (by linarith)
    -- Pick u = min (s + δ/2) t, strictly > s if s < t.
    set u := min (s + δ / 2) t with hu_def
    have hsu : s < u :=
      lt_min (by linarith) hs_lt_t
    have hu_le_t : u ≤ t := min_le_right _ _
    have hu_mem_Icc : u ∈ Set.Icc (0 : ℝ) t :=
      ⟨le_trans hs_nn (le_of_lt hsu), hu_le_t⟩
    have hu_dist : dist u s < δ := by
      have h1 : u ≤ s + δ / 2 := min_le_left _ _
      rw [Real.dist_eq, abs_of_pos (by linarith : (0:ℝ) < u - s)]
      linarith
    have h_apply := hδ_prop hu_mem_Icc hu_dist
    rw [Real.dist_eq] at h_apply
    have := abs_sub_lt_iff.mp h_apply
    have hu_in_S : u ∈ S := ⟨hu_mem_Icc, by linarith⟩
    have : u ≤ s := le_csSup hS_bdd hu_in_S
    linarith
  -- On (s, t], y u > U (complement of S within Icc 0 t via sSup).
  have hy_gt_on : ∀ u, s < u → u ≤ t → U < y u := by
    intro u hsu hut
    by_contra h_u_le
    push_neg at h_u_le
    have hu_in_S : u ∈ S :=
      ⟨⟨le_trans hs_nn (le_of_lt hsu), hut⟩, h_u_le⟩
    have : u ≤ s := le_csSup hS_bdd hu_in_S
    linarith
  -- Apply ODE uniqueness on [s, t] between y and the constant function U.
  have hy_cont_st : ContinuousOn y (Set.Icc s t) :=
    hy_cont.mono (fun u hu => ⟨le_trans hs_nn hu.1, hu.2⟩)
  have hx_cont_st : ContinuousOn x (Set.Icc s t) :=
    hx_cont.mono (fun u hu =>
      ⟨le_trans hs_nn hu.1, le_trans hu.2 ht_lt.le⟩)
  have h_st_ne : (Set.Icc s t).Nonempty :=
    ⟨s, ⟨le_refl _, hs_lt_t.le⟩⟩
  -- R bounds |y| and |x| on [s, t] via extreme value theorem.
  obtain ⟨u_y, hu_y_mem, hu_y_max⟩ :=
    isCompact_Icc.exists_isMaxOn h_st_ne hy_cont_st.abs
  obtain ⟨u_x, hu_x_mem, hu_x_max⟩ :=
    isCompact_Icc.exists_isMaxOn h_st_ne hx_cont_st.abs
  set R : ℝ := |y u_y| + |x u_x| + U + 1 with hR_def
  have hR_pos : 0 < R := by
    have h1 : 0 ≤ |y u_y| := abs_nonneg _
    have h2 : 0 ≤ |x u_x| := abs_nonneg _
    linarith
  have hy_bdd : ∀ u ∈ Set.Icc s t, |y u| ≤ R := by
    intro u hu
    have h1 : |y u| ≤ |y u_y| := hu_y_max hu
    linarith [abs_nonneg (x u_x)]
  have hx_bdd : ∀ u ∈ Set.Icc s t, |x u| ≤ R := by
    intro u hu
    have h1 : |x u| ≤ |x u_x| := hu_x_max hu
    linarith [abs_nonneg (y u_y)]
  -- Vector field v(u, z) := (x u - z)(U - z).
  let v : ℝ → ℝ → ℝ := fun u z => (x u - z) * (U - z)
  set K_val : ℝ := 3 * R + U with hK_val_def
  have hK_nn : 0 ≤ K_val := by
    show (0 : ℝ) ≤ 3 * R + U
    linarith
  let K : NNReal := Real.toNNReal K_val
  have hK_coe : (K : ℝ) = K_val := Real.coe_toNNReal K_val hK_nn
  -- Lipschitz on [-R, R] with constant K.
  have hv_lip : ∀ u ∈ Set.Ico s t, LipschitzOnWith K (v u) (Set.Icc (-R) R) := by
    intro u hu
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro z hz z' hz'
    rw [Real.dist_eq, Real.dist_eq, hK_coe]
    have hxu_abs : |x u| ≤ R :=
      hx_bdd u ⟨hu.1, le_of_lt hu.2⟩
    have hz_abs : |z| ≤ R := abs_le.mpr hz
    have hz'_abs : |z'| ≤ R := abs_le.mpr hz'
    have h_exp : v u z - v u z' = (z - z') * (-(x u) - U + z + z') := by
      simp only [v]; ring
    rw [h_exp, abs_mul]
    have h_factor : |-(x u) - U + z + z'| ≤ 3 * R + U := by
      have hxu_neg : -R ≤ -(x u) ∧ -(x u) ≤ R := by
        rcases abs_le.mp hxu_abs with ⟨l, r⟩
        exact ⟨by linarith, by linarith⟩
      rcases abs_le.mp hz_abs with ⟨hzl, hzr⟩
      rcases abs_le.mp hz'_abs with ⟨hz'l, hz'r⟩
      have hU_nn : 0 ≤ U := hU_pos.le
      rw [abs_le]
      refine ⟨?_, ?_⟩ <;> · nlinarith [hxu_neg.1, hxu_neg.2]
    have h_prod : |z - z'| * |-(x u) - U + z + z'|
        ≤ |z - z'| * (3 * R + U) :=
      mul_le_mul_of_nonneg_left h_factor (abs_nonneg _)
    have h_comm : |z - z'| * (3 * R + U) = (3 * R + U) * |z - z'| :=
      mul_comm _ _
    calc |z - z'| * |-(x u) - U + z + z'|
        ≤ |z - z'| * (3 * R + U) := h_prod
      _ = (3 * R + U) * |z - z'| := h_comm
      _ = K_val * |z - z'| := by rw [hK_val_def]
  let c : ℝ → ℝ := fun _ => U
  have hc_cont : ContinuousOn c (Set.Icc s t) := continuousOn_const
  have hc_deriv : ∀ u ∈ Set.Ico s t,
      HasDerivWithinAt c (v u (c u)) (Set.Ici u) u := by
    intro u _
    have h_v : v u (c u) = 0 := by simp [v, c]
    rw [h_v]
    exact (hasDerivAt_const u U).hasDerivWithinAt
  have hy_within : ∀ u ∈ Set.Ico s t,
      HasDerivWithinAt y (v u (y u)) (Set.Ici u) u := by
    intro u ⟨hu1, hu2⟩
    have hu_nn : 0 ≤ u := le_trans hs_nn hu1
    have hu_lt_T : u < T := lt_trans hu2 ht_lt
    exact (hy_deriv u hu_nn hu_lt_T).hasDerivWithinAt
  have hy_in_s : ∀ u ∈ Set.Ico s t, y u ∈ Set.Icc (-R) R := by
    intro u hu
    exact abs_le.mp (hy_bdd u ⟨hu.1, le_of_lt hu.2⟩)
  have hc_in_s : ∀ u ∈ Set.Ico s t, c u ∈ Set.Icc (-R) R := by
    intro u _
    show U ∈ Set.Icc (-R) R
    refine ⟨?_, ?_⟩ <;> · have h1 := abs_nonneg (y u_y); have h2 := abs_nonneg (x u_x); linarith
  have h_eq_at : y s = c s := hys_eq
  have hst_eqOn : Set.EqOn y c (Set.Icc s t) :=
    ODE_solution_unique_of_mem_Icc_right hv_lip hy_cont_st hy_within hy_in_s
      hc_cont hc_deriv hc_in_s h_eq_at
  have : y t = U := hst_eqOn ⟨hs_lt_t.le, le_refl _⟩
  linarith

/-! ## Step 5: analytic residual — existence of the saturating tracker solution.

Given a CBTC for `α` and any `U ∈ (α, 1) ∩ ℚ`, the extended system
`saturatingPIVP` has a solution on `[0, ∞)` extending the original trajectory
on the first `d` coordinates, with `y(t) ∈ [0, U]` and `y(t) → α` at an
explicit rate. This is the analytic content Mathlib does not give directly;
the paper-level argument is in `notes/saturating-surrogate-LPP.tex`.

Packaging as a single existential mirrors `relaxation_tracker_solution` in
`AddRationalPos.lean`. -/

/-! ### Phase B2: global existence of the extended trajectory.

Given `cbtc` and `U` with `0 < U`, the extended PIVP has a global-in-time
solution starting from `Fin.snoc (cbtc.sol.trajectory 0) 0`. The a priori bound is
`M := M_cbtc + U + 1`, where `M_cbtc` bounds the original trajectory.

The a priori invariance argument:
* the head `y_head := fun τ i => y τ i.castSucc` satisfies the original PIVP
  with initial data `cbtc.sol.trajectory 0` (via `evalField_castSucc`);
* ODE uniqueness on any compact sub-interval identifies `y_head` with
  `cbtc.sol.trajectory`, which inherits the bound `‖y_head t‖ ≤ M_cbtc`;
* the tail `y_last` satisfies the scalar tracker ODE driven by
  `y_head _ P.output.castSucc = cbtc.sol.trajectory _ P.output ≥ 0`
  (by CRN non-negativity), so the barriers give `y_last t ∈ [0, U]`;
* combining, `‖y t‖ ≤ max M_cbtc U ≤ M`.
-/

/-- **Phase B2.** Global existence of a trajectory of the extended saturating
system, starting at `Fin.snoc (cbtc.sol.trajectory 0) 0`. -/
lemma saturating_global_solution {d : ℕ} {α : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d α)
    (pcd : PolyCRNDecomposition d cbtc.pivp)
    (U : ℚ) (hU_nn : (0 : ℝ) ≤ (U : ℝ)) (hU_pos : (0 : ℝ) < (U : ℝ)) :
    ∃ y : ℝ → Fin (d+1) → ℝ,
      y 0 = Fin.snoc (cbtc.sol.trajectory 0) (0 : ℝ) ∧
      ∀ t : ℝ, 0 ≤ t →
        HasDerivAt (fun τ => y τ) ((saturatingPIVP cbtc.pivp U).toPIVP.field (y t)) t := by
  classical
  -- Extract cbtc's own a priori bound M_cbtc.
  obtain ⟨M_cbtc, hM_cbtc_pos, hM_cbtc_bd⟩ := cbtc.bounded
  -- Non-negativity of the original trajectory at every coordinate (needs pcd).
  have h_traj_nn : ∀ t : ℝ, 0 ≤ t → ∀ i : Fin d,
      0 ≤ cbtc.sol.trajectory t i := by
    intro t ht i
    have h_crn : IsCRNImplementable d cbtc.pivp.toPIVP.field :=
      pcd.toIsCRNImplementable
    have h_lip := polyPIVP_field_locally_lipschitz cbtc.pivp
    have h_init_nn : ∀ j, 0 ≤ cbtc.pivp.toPIVP.init j := by
      intro j
      simp only [PolyPIVP.toPIVP_init]
      exact_mod_cast pcd.init_nonneg j
    exact pivp_solution_nonneg h_crn h_lip h_init_nn cbtc.sol t ht i
  -- Set M := M_cbtc + U + 1.
  set M : ℝ := M_cbtc + (U : ℝ) + 1 with hM_def
  have hM_pos : 0 < M := by positivity
  -- Extended field Lipschitz.
  have h_lip := saturatingPIVP_field_locally_lipschitz cbtc.pivp U
  -- Initial condition for the extended system.
  set y₀ : Fin (d+1) → ℝ := Fin.snoc (cbtc.sol.trajectory 0) (0 : ℝ) with hy₀_def
  -- The a priori invariance hypothesis.
  have h_invariant : ∀ (T : ℝ), 0 < T → ∀ (y : ℝ → Fin (d+1) → ℝ),
      y 0 = y₀ →
      (∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivAt y
        ((saturatingPIVP cbtc.pivp U).toPIVP.field (y t)) t) →
      ∀ t ∈ Set.Ico (0 : ℝ) T, ‖y t‖ ≤ M := by
    intro T hT y hy_init hy_deriv t ht_mem
    -- Split y into head (first d coordinates) and last coordinate.
    set y_head : ℝ → Fin d → ℝ := fun τ i => y τ i.castSucc with hy_head_def
    set y_last : ℝ → ℝ := fun τ => y τ (Fin.last d) with hy_last_def
    -- (a) y_head 0 = cbtc.sol.trajectory 0.
    have hy_head_init : y_head 0 = cbtc.sol.trajectory 0 := by
      funext i
      show y 0 i.castSucc = cbtc.sol.trajectory 0 i
      rw [hy_init]
      simp [y₀, Fin.snoc_castSucc]
    have hy_head_init' : y_head 0 = cbtc.pivp.toPIVP.init := by
      rw [hy_head_init]; exact cbtc.sol.init_cond
    -- (b) y_head satisfies the original PIVP on Ico 0 T.
    have hy_head_deriv : ∀ τ ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt y_head (cbtc.pivp.toPIVP.field (y_head τ)) τ := by
      intro τ hτ
      rw [hasDerivAt_pi]
      intro i
      have h_full := hy_deriv τ hτ
      have h_i := (hasDerivAt_pi.mp h_full) i.castSucc
      -- Rewrite field value via evalField_castSucc.
      have h_eval := evalField_castSucc cbtc.pivp U (y τ) i
      -- The function (fun τ => y τ i.castSucc) equals y_head · i.
      show HasDerivAt (fun τ => y τ i.castSucc)
        (cbtc.pivp.toPIVP.field (y_head τ) i) τ
      rw [← h_eval]
      exact h_i
    -- (c) cbtc.sol.trajectory also satisfies the PIVP starting from the same init.
    have h_cbtc_deriv : ∀ τ ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt cbtc.sol.trajectory
          (cbtc.pivp.toPIVP.field (cbtc.sol.trajectory τ)) τ := by
      intro τ hτ
      exact cbtc.sol.is_solution τ hτ.1
    have h_cbtc_init : cbtc.sol.trajectory 0 = cbtc.pivp.toPIVP.init :=
      cbtc.sol.init_cond
    -- (d) Uniqueness: y_head = cbtc.sol.trajectory on Ico 0 T.
    -- Apply solutions_agree_on_Icc on a strictly smaller interval [0, T'] with t < T'.
    -- Pick T' := (t + T) / 2 < T so that t ∈ Icc 0 T' ⊂ Ico 0 T.
    have ht_lt_T : t < T := ht_mem.2
    set T' : ℝ := (t + T) / 2 with hT'_def
    have hT'_lt_T : T' < T := by
      show (t + T) / 2 < T; linarith [ht_mem.2]
    have ht_le_T' : t ≤ T' := by
      show t ≤ (t + T) / 2; linarith [ht_mem.2]
    have hT'_pos : 0 < T' := by
      have : 0 ≤ t := ht_mem.1
      linarith
    have hT'_nn : 0 ≤ T' := hT'_pos.le
    -- Bound on cbtc.sol.trajectory on Icc 0 T'.
    have h_cbtc_bd_T' : ∀ τ ∈ Set.Icc (0 : ℝ) T', ‖cbtc.sol.trajectory τ‖ ≤ M_cbtc := by
      intro τ hτ
      exact hM_cbtc_bd τ hτ.1
    -- We want to bound y_head on Icc 0 T' using uniqueness — but first we need
    -- y_head bounded by some Mhd so that solutions_agree_on_Icc applies. Strategy:
    -- use the already-assumed bound ‖y τ‖ ≤ M on Ico 0 T (from hy_deriv via local
    -- Lipschitz, but we don't have this). Instead, a priori we only know y has
    -- HasDerivAt. To apply solutions_agree_on_Icc, use h_lip on a common bound.
    -- Take R := max M_cbtc (sup on Icc 0 T' of ‖y_head‖).
    -- Since y_head is continuous on Icc 0 T' (from HasDerivAt on Ico 0 T ⊇ Icc 0 T'),
    -- attains its max; call it M_y.
    have hy_head_cont : ContinuousOn y_head (Set.Icc 0 T') := by
      intro τ hτ
      have hτ_Ico : τ ∈ Set.Ico (0 : ℝ) T :=
        ⟨hτ.1, lt_of_le_of_lt hτ.2 hT'_lt_T⟩
      exact (hy_head_deriv τ hτ_Ico).continuousAt.continuousWithinAt
    have hy_head_cont_norm : ContinuousOn (fun τ => ‖y_head τ‖) (Set.Icc 0 T') :=
      hy_head_cont.norm
    have h_Icc_ne : (Set.Icc (0 : ℝ) T').Nonempty := ⟨0, ⟨le_refl _, hT'_nn⟩⟩
    obtain ⟨u_y, _, hu_y_max⟩ :=
      isCompact_Icc.exists_isMaxOn h_Icc_ne hy_head_cont_norm
    set My : ℝ := ‖y_head u_y‖ with hMy_def
    have hMy_nn : 0 ≤ My := norm_nonneg _
    have hy_head_bd_T' : ∀ τ ∈ Set.Icc (0 : ℝ) T', ‖y_head τ‖ ≤ My := fun τ hτ =>
      hu_y_max hτ
    -- Common bound R := max M_cbtc My.
    set R : ℝ := max M_cbtc My with hR_def
    have hR_nn : 0 ≤ R := le_max_of_le_left hM_cbtc_pos.le
    have hy_head_bd_R : ∀ τ ∈ Set.Icc (0 : ℝ) T', ‖y_head τ‖ ≤ R := fun τ hτ =>
      le_trans (hy_head_bd_T' τ hτ) (le_max_right _ _)
    have h_cbtc_bd_R : ∀ τ ∈ Set.Icc (0 : ℝ) T', ‖cbtc.sol.trajectory τ‖ ≤ R :=
      fun τ hτ => le_trans (h_cbtc_bd_T' τ hτ) (le_max_left _ _)
    -- Apply solutions_agree_on_Icc to y_head and cbtc.sol.trajectory on Icc 0 T'.
    have h_lip_orig := polyPIVP_field_locally_lipschitz cbtc.pivp
    have hy_head_dw : ∀ τ ∈ Set.Icc (0 : ℝ) T',
        HasDerivWithinAt y_head (cbtc.pivp.toPIVP.field (y_head τ))
          (Set.Icc 0 T') τ := by
      intro τ hτ
      have hτ_Ico : τ ∈ Set.Ico (0 : ℝ) T :=
        ⟨hτ.1, lt_of_le_of_lt hτ.2 hT'_lt_T⟩
      exact (hy_head_deriv τ hτ_Ico).hasDerivWithinAt
    have h_cbtc_dw : ∀ τ ∈ Set.Icc (0 : ℝ) T',
        HasDerivWithinAt cbtc.sol.trajectory
          (cbtc.pivp.toPIVP.field (cbtc.sol.trajectory τ))
          (Set.Icc 0 T') τ := by
      intro τ hτ
      have hτ_Ico : τ ∈ Set.Ico (0 : ℝ) T :=
        ⟨hτ.1, lt_of_le_of_lt hτ.2 hT'_lt_T⟩
      exact (h_cbtc_deriv τ hτ_Ico).hasDerivWithinAt
    have h_eqOn : Set.EqOn y_head cbtc.sol.trajectory (Set.Icc 0 T') :=
      solutions_agree_on_Icc hT'_pos hR_nn h_lip_orig
        hy_head_init' h_cbtc_init hy_head_dw h_cbtc_dw hy_head_bd_R h_cbtc_bd_R
    -- Therefore ‖y_head t‖ ≤ M_cbtc (via cbtc.bounded).
    have ht_in_Icc_T' : t ∈ Set.Icc (0 : ℝ) T' := ⟨ht_mem.1, ht_le_T'⟩
    have hy_head_t_eq : y_head t = cbtc.sol.trajectory t := h_eqOn ht_in_Icc_T'
    have hy_head_t_bd : ‖y_head t‖ ≤ M_cbtc := by
      rw [hy_head_t_eq]; exact hM_cbtc_bd t ht_mem.1
    -- (e) y_last ∈ [0, U] on Ico 0 T via the barriers.
    -- Build x(τ) := y_head τ cbtc.pivp.output.castSucc = y τ cbtc.pivp.output.castSucc.
    set x_fn : ℝ → ℝ := fun τ => y τ cbtc.pivp.output.castSucc with hx_fn_def
    -- x_fn ≥ 0 on Ico 0 T.
    have hx_nn : ∀ τ, 0 ≤ τ → τ < T → 0 ≤ x_fn τ := by
      intro τ hτ_nn hτ_lt
      · set T'' : ℝ := (τ + T) / 2 with hT''_def
        have hT''_lt_T : T'' < T := by show (τ + T) / 2 < T; linarith
        have hτ_le_T'' : τ ≤ T'' := by show τ ≤ (τ + T) / 2; linarith
        have hT''_pos : 0 < T'' := by linarith
        have hT''_nn : 0 ≤ T'' := hT''_pos.le
        -- Repeat the agreement argument on Icc 0 T''.
        have hy_head_cont'' : ContinuousOn y_head (Set.Icc 0 T'') := by
          intro τ' hτ'
          have hτ'_Ico : τ' ∈ Set.Ico (0 : ℝ) T :=
            ⟨hτ'.1, lt_of_le_of_lt hτ'.2 hT''_lt_T⟩
          exact (hy_head_deriv τ' hτ'_Ico).continuousAt.continuousWithinAt
        have hy_head_cont_norm'' : ContinuousOn (fun τ' => ‖y_head τ'‖) (Set.Icc 0 T'') :=
          hy_head_cont''.norm
        have h_Icc_ne'' : (Set.Icc (0 : ℝ) T'').Nonempty := ⟨0, ⟨le_refl _, hT''_nn⟩⟩
        obtain ⟨u_y'', _, hu_y_max''⟩ :=
          isCompact_Icc.exists_isMaxOn h_Icc_ne'' hy_head_cont_norm''
        set My'' : ℝ := ‖y_head u_y''‖ with hMy''_def
        set R'' : ℝ := max M_cbtc My'' with hR''_def
        have hR''_nn : 0 ≤ R'' := le_max_of_le_left hM_cbtc_pos.le
        have hy_head_bd_R'' : ∀ s ∈ Set.Icc (0 : ℝ) T'', ‖y_head s‖ ≤ R'' := fun s hs =>
          le_trans (hu_y_max'' hs) (le_max_right _ _)
        have h_cbtc_bd_R'' : ∀ s ∈ Set.Icc (0 : ℝ) T'', ‖cbtc.sol.trajectory s‖ ≤ R'' := by
          intro s hs
          exact le_trans (hM_cbtc_bd s hs.1) (le_max_left _ _)
        have hy_head_dw'' : ∀ s ∈ Set.Icc (0 : ℝ) T'',
            HasDerivWithinAt y_head (cbtc.pivp.toPIVP.field (y_head s))
              (Set.Icc 0 T'') s := by
          intro s hs
          have hs_Ico : s ∈ Set.Ico (0 : ℝ) T :=
            ⟨hs.1, lt_of_le_of_lt hs.2 hT''_lt_T⟩
          exact (hy_head_deriv s hs_Ico).hasDerivWithinAt
        have h_cbtc_dw'' : ∀ s ∈ Set.Icc (0 : ℝ) T'',
            HasDerivWithinAt cbtc.sol.trajectory
              (cbtc.pivp.toPIVP.field (cbtc.sol.trajectory s))
              (Set.Icc 0 T'') s := by
          intro s hs
          have hs_Ico : s ∈ Set.Ico (0 : ℝ) T :=
            ⟨hs.1, lt_of_le_of_lt hs.2 hT''_lt_T⟩
          exact (h_cbtc_deriv s hs_Ico).hasDerivWithinAt
        have h_eqOn'' : Set.EqOn y_head cbtc.sol.trajectory (Set.Icc 0 T'') :=
          solutions_agree_on_Icc hT''_pos hR''_nn h_lip_orig
            hy_head_init' h_cbtc_init hy_head_dw'' h_cbtc_dw'' hy_head_bd_R''
            h_cbtc_bd_R''
        have hτ_in'' : τ ∈ Set.Icc (0 : ℝ) T'' := ⟨hτ_nn, hτ_le_T''⟩
        have h_x_eq : x_fn τ = cbtc.sol.trajectory τ cbtc.pivp.output := by
          show y τ cbtc.pivp.output.castSucc = _
          have := h_eqOn'' hτ_in''
          show y_head τ cbtc.pivp.output = _
          rw [this]
        rw [h_x_eq]
        exact h_traj_nn τ hτ_nn cbtc.pivp.output
    -- y_last has derivative equal to (x_fn - y_last)(U - y_last) on Ico 0 T.
    have hy_last_deriv : ∀ τ, 0 ≤ τ → τ < T →
        HasDerivAt y_last ((x_fn τ - y_last τ) * ((U : ℝ) - y_last τ)) τ := by
      intro τ hτ_nn hτ_lt_T
      have hτ_Ico : τ ∈ Set.Ico (0 : ℝ) T := ⟨hτ_nn, hτ_lt_T⟩
      have h_full := hy_deriv τ hτ_Ico
      have h_last := (hasDerivAt_pi.mp h_full) (Fin.last d)
      -- Rewrite the field value using evalField_last.
      have h_eval := evalField_last cbtc.pivp U (y τ)
      show HasDerivAt (fun τ => y τ (Fin.last d))
        ((x_fn τ - y_last τ) * ((U : ℝ) - y_last τ)) τ
      have h_rewrite :
          ((y τ cbtc.pivp.output.castSucc - y τ (Fin.last d)) *
              ((U : ℝ) - y τ (Fin.last d)))
            = (x_fn τ - y_last τ) * ((U : ℝ) - y_last τ) := rfl
      rw [← h_rewrite, ← h_eval]
      exact h_last
    -- y_last 0 = 0.
    have hy_last_0 : y_last 0 = 0 := by
      show y 0 (Fin.last d) = 0
      rw [hy_init]; simp [y₀, Fin.snoc_last]
    -- x_fn continuous on Icc 0 T'.
    have hx_fn_cont_T' : ContinuousOn x_fn (Set.Icc 0 T') := by
      intro τ hτ
      have hτ_Ico : τ ∈ Set.Ico (0 : ℝ) T :=
        ⟨hτ.1, lt_of_le_of_lt hτ.2 hT'_lt_T⟩
      have h_full := hy_deriv τ hτ_Ico
      have h_comp := (hasDerivAt_pi.mp h_full) cbtc.pivp.output.castSucc
      exact h_comp.continuousAt.continuousWithinAt
    -- Apply upper barrier on [0, T']: y_last t ≤ U, since t < T'.
    have hy_last_upper : y_last t ≤ (U : ℝ) := by
      have ht_lt_T' : t < T' ∨ t = T' := lt_or_eq_of_le ht_le_T'
      rcases ht_lt_T' with h_lt | h_eq
      · -- t < T', so t ∈ Ico 0 T'.
        have hdy_Ico : ∀ τ, 0 ≤ τ → τ < T' →
            HasDerivAt y_last ((x_fn τ - y_last τ) * ((U : ℝ) - y_last τ)) τ := by
          intro τ hτ_nn hτ_lt_T'
          have hτ_lt_T : τ < T := lt_trans hτ_lt_T' hT'_lt_T
          exact hy_last_deriv τ hτ_nn hτ_lt_T
        exact saturating_barrier_upper hU_pos hx_fn_cont_T' hy_last_0 hdy_Ico t
          ht_mem.1 h_lt
      · -- t = T', impossible strictly... actually t = T' is fine. Pick smaller T''.
        -- Use T'' := (t + T) / 2 > t to ensure strict.
        set T'' : ℝ := (t + T) / 2 with hT''_def
        have hT''_lt_T : T'' < T := by show (t + T) / 2 < T; linarith [ht_mem.2]
        have ht_lt_T'' : t < T'' := by show t < (t + T) / 2; linarith [ht_mem.2]
        have hT''_pos : 0 < T'' := by linarith [ht_mem.1]
        have hx_fn_cont_T'' : ContinuousOn x_fn (Set.Icc 0 T'') := by
          intro τ hτ
          have hτ_Ico : τ ∈ Set.Ico (0 : ℝ) T :=
            ⟨hτ.1, lt_of_le_of_lt hτ.2 hT''_lt_T⟩
          have h_full := hy_deriv τ hτ_Ico
          have h_comp := (hasDerivAt_pi.mp h_full) cbtc.pivp.output.castSucc
          exact h_comp.continuousAt.continuousWithinAt
        have hdy_Ico : ∀ τ, 0 ≤ τ → τ < T'' →
            HasDerivAt y_last ((x_fn τ - y_last τ) * ((U : ℝ) - y_last τ)) τ := by
          intro τ hτ_nn hτ_lt_T''
          have hτ_lt_T : τ < T := lt_trans hτ_lt_T'' hT''_lt_T
          exact hy_last_deriv τ hτ_nn hτ_lt_T
        exact saturating_barrier_upper hU_pos hx_fn_cont_T'' hy_last_0 hdy_Ico t
          ht_mem.1 ht_lt_T''
    -- Apply lower barrier similarly.
    have hy_last_lower : 0 ≤ y_last t := by
      set T'' : ℝ := (t + T) / 2 with hT''_def
      have hT''_lt_T : T'' < T := by show (t + T) / 2 < T; linarith [ht_mem.2]
      have ht_lt_T'' : t < T'' := by show t < (t + T) / 2; linarith [ht_mem.2]
      have hT''_pos : 0 < T'' := by linarith [ht_mem.1]
      -- We need hx_nn on [0, T''], which requires the uniqueness argument.
      have hx_nn_T'' : ∀ τ, 0 ≤ τ → τ ≤ T'' → 0 ≤ x_fn τ := by
        intro τ hτ_nn hτ_le_T''
        have hτ_lt_T : τ < T := lt_of_le_of_lt hτ_le_T'' hT''_lt_T
        exact hx_nn τ hτ_nn hτ_lt_T
      have hdy_Ico : ∀ τ, 0 ≤ τ → τ < T'' →
          HasDerivAt y_last ((x_fn τ - y_last τ) * ((U : ℝ) - y_last τ)) τ := by
        intro τ hτ_nn hτ_lt_T''
        have hτ_lt_T : τ < T := lt_trans hτ_lt_T'' hT''_lt_T
        exact hy_last_deriv τ hτ_nn hτ_lt_T
      exact saturating_barrier_lower hU_pos hx_nn_T'' hy_last_0 hdy_Ico t
        ht_mem.1 ht_lt_T''
    -- (f) Combine bounds.
    rw [pi_norm_le_iff_of_nonneg hM_pos.le]
    intro k
    refine Fin.lastCases ?_ (fun i => ?_) k
    · -- Last coord: |y_last t| ≤ U ≤ M.
      show ‖y t (Fin.last d)‖ ≤ M
      have h_y_last_val : y t (Fin.last d) = y_last t := rfl
      rw [h_y_last_val, Real.norm_eq_abs, abs_le]
      refine ⟨?_, ?_⟩
      · linarith
      · linarith
    · -- castSucc: ‖y t i.castSucc‖ ≤ ‖y_head t‖ ≤ M_cbtc ≤ M.
      show ‖y t i.castSucc‖ ≤ M
      have h_eq : y t i.castSucc = y_head t i := rfl
      rw [h_eq]
      have h1 : ‖y_head t i‖ ≤ ‖y_head t‖ := norm_le_pi_norm _ _
      have h2 : ‖y_head t‖ ≤ M_cbtc := hy_head_t_bd
      linarith
  -- Apply the global existence theorem.
  exact
    locally_lipschitz_bounded_global_ode_proved
      (saturatingPIVP cbtc.pivp U).toPIVP.field y₀ h_lip M hM_pos h_invariant

/-! ### Phase C+E helper: agreement and output-range on a finite window.

Given any `y` on the extended system with the correct initial condition and
derivative on `Ico 0 T`, we get three invariants on `Ico 0 T`:

(i) `y τ i.castSucc = cbtc.sol.trajectory τ i` (head matching, via uniqueness),
(ii) `0 ≤ y τ (Fin.last d)` (lower barrier),
(iii) `y τ (Fin.last d) ≤ (U : ℝ)` (upper barrier).

This is the same argument used inside `saturating_global_solution`'s
`h_invariant`, re-packaged so Phase C+E can reuse it. -/
lemma saturating_agrees_on_Ico {d : ℕ} {α : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d α)
    (pcd : PolyCRNDecomposition d cbtc.pivp)
    (U : ℚ) (hU_nn : (0 : ℝ) ≤ (U : ℝ)) (hU_pos : (0 : ℝ) < (U : ℝ))
    {T : ℝ} (hT : 0 < T)
    (y : ℝ → Fin (d+1) → ℝ)
    (hy_init : y 0 = Fin.snoc (cbtc.sol.trajectory 0) (0 : ℝ))
    (hy_deriv : ∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivAt y
        ((saturatingPIVP cbtc.pivp U).toPIVP.field (y t)) t) :
    (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i : Fin d,
        y t i.castSucc = cbtc.sol.trajectory t i) ∧
    (∀ t ∈ Set.Ico (0 : ℝ) T,
        0 ≤ y t (Fin.last d) ∧ y t (Fin.last d) ≤ (U : ℝ)) := by
  classical
  -- Extract cbtc's own a priori bound M_cbtc.
  obtain ⟨M_cbtc, hM_cbtc_pos, hM_cbtc_bd⟩ := cbtc.bounded
  -- Non-negativity of the original trajectory at every coordinate (needs pcd).
  have h_traj_nn : ∀ t : ℝ, 0 ≤ t → ∀ i : Fin d,
      0 ≤ cbtc.sol.trajectory t i := by
    intro t ht i
    have h_crn : IsCRNImplementable d cbtc.pivp.toPIVP.field :=
      pcd.toIsCRNImplementable
    have h_lip := polyPIVP_field_locally_lipschitz cbtc.pivp
    have h_init_nn : ∀ j, 0 ≤ cbtc.pivp.toPIVP.init j := by
      intro j
      simp only [PolyPIVP.toPIVP_init]
      exact_mod_cast pcd.init_nonneg j
    exact pivp_solution_nonneg h_crn h_lip h_init_nn cbtc.sol t ht i
  -- Split y into head (first d coordinates) and last coordinate.
  set y_head : ℝ → Fin d → ℝ := fun τ i => y τ i.castSucc with hy_head_def
  set y_last : ℝ → ℝ := fun τ => y τ (Fin.last d) with hy_last_def
  -- (a) y_head 0 = cbtc.sol.trajectory 0.
  have hy_head_init : y_head 0 = cbtc.sol.trajectory 0 := by
    funext i
    show y 0 i.castSucc = cbtc.sol.trajectory 0 i
    rw [hy_init]
    simp [Fin.snoc_castSucc]
  have hy_head_init' : y_head 0 = cbtc.pivp.toPIVP.init := by
    rw [hy_head_init]; exact cbtc.sol.init_cond
  -- (b) y_head satisfies the original PIVP on Ico 0 T.
  have hy_head_deriv : ∀ τ ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt y_head (cbtc.pivp.toPIVP.field (y_head τ)) τ := by
    intro τ hτ
    rw [hasDerivAt_pi]
    intro i
    have h_full := hy_deriv τ hτ
    have h_i := (hasDerivAt_pi.mp h_full) i.castSucc
    have h_eval := evalField_castSucc cbtc.pivp U (y τ) i
    show HasDerivAt (fun τ => y τ i.castSucc)
      (cbtc.pivp.toPIVP.field (y_head τ) i) τ
    rw [← h_eval]
    exact h_i
  -- (c) cbtc.sol.trajectory also satisfies the PIVP starting from the same init.
  have h_cbtc_deriv : ∀ τ ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt cbtc.sol.trajectory
        (cbtc.pivp.toPIVP.field (cbtc.sol.trajectory τ)) τ := by
    intro τ hτ
    exact cbtc.sol.is_solution τ hτ.1
  have h_cbtc_init : cbtc.sol.trajectory 0 = cbtc.pivp.toPIVP.init :=
    cbtc.sol.init_cond
  have h_lip_orig := polyPIVP_field_locally_lipschitz cbtc.pivp
  -- Agreement on any sub-interval [0, S] ⊂ [0, T).
  have h_agree : ∀ S : ℝ, 0 < S → S < T →
      Set.EqOn y_head cbtc.sol.trajectory (Set.Icc 0 S) := by
    intro S hS_pos hS_lt_T
    have hS_nn : 0 ≤ S := hS_pos.le
    -- Continuity of y_head on [0, S].
    have hy_head_cont : ContinuousOn y_head (Set.Icc 0 S) := by
      intro τ hτ
      have hτ_Ico : τ ∈ Set.Ico (0 : ℝ) T :=
        ⟨hτ.1, lt_of_le_of_lt hτ.2 hS_lt_T⟩
      exact (hy_head_deriv τ hτ_Ico).continuousAt.continuousWithinAt
    have hy_head_cont_norm : ContinuousOn (fun τ => ‖y_head τ‖) (Set.Icc 0 S) :=
      hy_head_cont.norm
    have h_Icc_ne : (Set.Icc (0 : ℝ) S).Nonempty := ⟨0, ⟨le_refl _, hS_nn⟩⟩
    obtain ⟨u_y, _, hu_y_max⟩ :=
      isCompact_Icc.exists_isMaxOn h_Icc_ne hy_head_cont_norm
    set My : ℝ := ‖y_head u_y‖ with hMy_def
    set R : ℝ := max M_cbtc My with hR_def
    have hR_nn : 0 ≤ R := le_max_of_le_left hM_cbtc_pos.le
    have hy_head_bd_R : ∀ τ ∈ Set.Icc (0 : ℝ) S, ‖y_head τ‖ ≤ R := fun τ hτ =>
      le_trans (hu_y_max hτ) (le_max_right _ _)
    have h_cbtc_bd_R : ∀ τ ∈ Set.Icc (0 : ℝ) S, ‖cbtc.sol.trajectory τ‖ ≤ R :=
      fun τ hτ => le_trans (hM_cbtc_bd τ hτ.1) (le_max_left _ _)
    have hy_head_dw : ∀ τ ∈ Set.Icc (0 : ℝ) S,
        HasDerivWithinAt y_head (cbtc.pivp.toPIVP.field (y_head τ))
          (Set.Icc 0 S) τ := by
      intro τ hτ
      have hτ_Ico : τ ∈ Set.Ico (0 : ℝ) T :=
        ⟨hτ.1, lt_of_le_of_lt hτ.2 hS_lt_T⟩
      exact (hy_head_deriv τ hτ_Ico).hasDerivWithinAt
    have h_cbtc_dw : ∀ τ ∈ Set.Icc (0 : ℝ) S,
        HasDerivWithinAt cbtc.sol.trajectory
          (cbtc.pivp.toPIVP.field (cbtc.sol.trajectory τ))
          (Set.Icc 0 S) τ := by
      intro τ hτ
      have hτ_Ico : τ ∈ Set.Ico (0 : ℝ) T :=
        ⟨hτ.1, lt_of_le_of_lt hτ.2 hS_lt_T⟩
      exact (h_cbtc_deriv τ hτ_Ico).hasDerivWithinAt
    exact solutions_agree_on_Icc hS_pos hR_nn h_lip_orig
      hy_head_init' h_cbtc_init hy_head_dw h_cbtc_dw hy_head_bd_R h_cbtc_bd_R
  -- Head matching: for t ∈ Ico 0 T, pick S = (t + T)/2.
  have h_head_match : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i : Fin d,
      y t i.castSucc = cbtc.sol.trajectory t i := by
    intro t ht_mem i
    set S : ℝ := (t + T) / 2 with hS_def
    have hS_lt_T : S < T := by show (t + T) / 2 < T; linarith [ht_mem.2]
    have ht_le_S : t ≤ S := by show t ≤ (t + T) / 2; linarith [ht_mem.2]
    have hS_pos : 0 < S := by linarith [ht_mem.1]
    have ht_in_Icc_S : t ∈ Set.Icc (0 : ℝ) S := ⟨ht_mem.1, ht_le_S⟩
    have h_eqOn := h_agree S hS_pos hS_lt_T
    have h_eq : y_head t = cbtc.sol.trajectory t := h_eqOn ht_in_Icc_S
    show y_head t i = cbtc.sol.trajectory t i
    rw [h_eq]
  -- Build x_fn := y τ cbtc.pivp.output.castSucc, and show x_fn ≥ 0 on Ico 0 T.
  set x_fn : ℝ → ℝ := fun τ => y τ cbtc.pivp.output.castSucc with hx_fn_def
  have hx_nn : ∀ τ, 0 ≤ τ → τ < T → 0 ≤ x_fn τ := by
    intro τ hτ_nn hτ_lt
    have : y τ cbtc.pivp.output.castSucc = cbtc.sol.trajectory τ cbtc.pivp.output :=
      h_head_match τ ⟨hτ_nn, hτ_lt⟩ cbtc.pivp.output
    show x_fn τ ≥ 0
    rw [show x_fn τ = y τ cbtc.pivp.output.castSucc from rfl, this]
    exact h_traj_nn τ hτ_nn cbtc.pivp.output
  -- y_last has derivative (x_fn - y_last)(U - y_last) on Ico 0 T.
  have hy_last_deriv : ∀ τ, 0 ≤ τ → τ < T →
      HasDerivAt y_last ((x_fn τ - y_last τ) * ((U : ℝ) - y_last τ)) τ := by
    intro τ hτ_nn hτ_lt_T
    have hτ_Ico : τ ∈ Set.Ico (0 : ℝ) T := ⟨hτ_nn, hτ_lt_T⟩
    have h_full := hy_deriv τ hτ_Ico
    have h_last := (hasDerivAt_pi.mp h_full) (Fin.last d)
    have h_eval := evalField_last cbtc.pivp U (y τ)
    show HasDerivAt (fun τ => y τ (Fin.last d))
      ((x_fn τ - y_last τ) * ((U : ℝ) - y_last τ)) τ
    have h_rewrite :
        ((y τ cbtc.pivp.output.castSucc - y τ (Fin.last d)) *
            ((U : ℝ) - y τ (Fin.last d)))
          = (x_fn τ - y_last τ) * ((U : ℝ) - y_last τ) := rfl
    rw [← h_rewrite, ← h_eval]
    exact h_last
  have hy_last_0 : y_last 0 = 0 := by
    show y 0 (Fin.last d) = 0
    rw [hy_init]; simp [Fin.snoc_last]
  -- Continuity of x_fn on [0, S] for S < T.
  have hx_fn_cont_on : ∀ S : ℝ, S < T → ContinuousOn x_fn (Set.Icc 0 S) := by
    intro S hS_lt_T τ hτ
    have hτ_Ico : τ ∈ Set.Ico (0 : ℝ) T :=
      ⟨hτ.1, lt_of_le_of_lt hτ.2 hS_lt_T⟩
    have h_full := hy_deriv τ hτ_Ico
    have h_comp := (hasDerivAt_pi.mp h_full) cbtc.pivp.output.castSucc
    exact h_comp.continuousAt.continuousWithinAt
  -- Combine: for t ∈ Ico 0 T, pick T'' := (t + T)/2 > t so that Ico 0 T'' ⊃ [0, t].
  have h_range : ∀ t ∈ Set.Ico (0 : ℝ) T,
      0 ≤ y t (Fin.last d) ∧ y t (Fin.last d) ≤ (U : ℝ) := by
    intro t ht_mem
    set T'' : ℝ := (t + T) / 2 with hT''_def
    have hT''_lt_T : T'' < T := by show (t + T) / 2 < T; linarith [ht_mem.2]
    have ht_lt_T'' : t < T'' := by show t < (t + T) / 2; linarith [ht_mem.2]
    have hT''_pos : 0 < T'' := by linarith [ht_mem.1]
    have hx_fn_cont_T'' : ContinuousOn x_fn (Set.Icc 0 T'') :=
      hx_fn_cont_on T'' hT''_lt_T
    have hdy_Ico : ∀ τ, 0 ≤ τ → τ < T'' →
        HasDerivAt y_last ((x_fn τ - y_last τ) * ((U : ℝ) - y_last τ)) τ := by
      intro τ hτ_nn hτ_lt_T''
      exact hy_last_deriv τ hτ_nn (lt_trans hτ_lt_T'' hT''_lt_T)
    have hx_nn_T'' : ∀ τ, 0 ≤ τ → τ ≤ T'' → 0 ≤ x_fn τ := by
      intro τ hτ_nn hτ_le_T''
      exact hx_nn τ hτ_nn (lt_of_le_of_lt hτ_le_T'' hT''_lt_T)
    refine ⟨?_, ?_⟩
    · -- Lower barrier.
      exact saturating_barrier_lower hU_pos hx_nn_T'' hy_last_0 hdy_Ico t
        ht_mem.1 ht_lt_T''
    · -- Upper barrier.
      exact saturating_barrier_upper hU_pos hx_fn_cont_T'' hy_last_0 hdy_Ico t
        ht_mem.1 ht_lt_T''
  exact ⟨h_head_match, h_range⟩

/-- **Phase C+E.** The extended PIVP admits a genuine `PIVP.Solution` which is
bounded and whose last coordinate stays in `[0, U]` on `t ≥ 0`. The third
conjunct — head matching — says the first `d` coordinates of the extended
trajectory coincide pointwise with `cbtc.sol.trajectory`. -/
lemma saturating_extended_solution {d : ℕ} {α : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d α)
    (pcd : PolyCRNDecomposition d cbtc.pivp)
    (U : ℚ) (hU_nn : (0 : ℝ) ≤ (U : ℝ)) (hU_pos : (0 : ℝ) < (U : ℝ)) :
    ∃ (sol' : PIVP.Solution (saturatingPIVP cbtc.pivp U).toPIVP),
      (saturatingPIVP cbtc.pivp U).toPIVP.IsBounded sol'.trajectory ∧
      (∀ σ : ℝ, 0 ≤ σ →
        0 ≤ sol'.trajectory σ (saturatingPIVP cbtc.pivp U).output ∧
        sol'.trajectory σ (saturatingPIVP cbtc.pivp U).output ≤ (U : ℝ)) ∧
      (∀ σ : ℝ, 0 ≤ σ → ∀ i : Fin d,
        sol'.trajectory σ i.castSucc = cbtc.sol.trajectory σ i) := by
  classical
  -- Get the global trajectory from Phase B2.
  obtain ⟨y, hy_init, hy_deriv_all⟩ :=
    saturating_global_solution cbtc pcd U hU_nn hU_pos
  -- Build the PIVP.Solution wrapper.
  have h_init_match : y 0 = (saturatingPIVP cbtc.pivp U).toPIVP.init := by
    rw [hy_init]
    funext k
    induction k using Fin.lastCases with
    | last =>
      -- Goal: Fin.snoc _ 0 (Fin.last d) = (satPIVP..).toPIVP.init (Fin.last d)
      rw [Fin.snoc_last]
      show (0 : ℝ) = ((saturatingPIVP cbtc.pivp U).init (Fin.last d) : ℝ)
      rw [saturatingPIVP_init_last]; norm_cast
    | cast i =>
      -- Goal: Fin.snoc _ 0 i.castSucc = (satPIVP..).toPIVP.init i.castSucc
      rw [Fin.snoc_castSucc]
      show cbtc.sol.trajectory 0 i = ((saturatingPIVP cbtc.pivp U).init i.castSucc : ℝ)
      rw [saturatingPIVP_init_castSucc]
      show cbtc.sol.trajectory 0 i = (cbtc.pivp.init i : ℝ)
      have h : cbtc.sol.trajectory 0 = cbtc.pivp.toPIVP.init := cbtc.sol.init_cond
      rw [h]; rfl
  let sol' : PIVP.Solution (saturatingPIVP cbtc.pivp U).toPIVP :=
    { trajectory := y
      init_cond := h_init_match
      is_solution := hy_deriv_all }
  refine ⟨sol', ?_, ?_, ?_⟩
  · -- IsBounded. Bound: M := (sup on [0, 1] of ‖y‖) + ... Actually simplest: use
    -- the head-matching to bound y on each coord via cbtc.bounded + U.
    obtain ⟨M_cbtc, hM_cbtc_pos, hM_cbtc_bd⟩ := cbtc.bounded
    set M : ℝ := M_cbtc + (U : ℝ) + 1 with hM_def
    have hM_pos : 0 < M := by positivity
    refine ⟨M, hM_pos, ?_⟩
    intro t ht
    -- Apply saturating_agrees_on_Ico on Ico 0 (t+1).
    set T : ℝ := t + 1 with hT_def
    have hT_pos : 0 < T := by linarith
    have ht_mem : t ∈ Set.Ico (0 : ℝ) T := ⟨ht, by linarith⟩
    have hy_deriv_Ico : ∀ τ ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt y ((saturatingPIVP cbtc.pivp U).toPIVP.field (y τ)) τ := by
      intro τ hτ
      exact hy_deriv_all τ hτ.1
    obtain ⟨h_head_match, h_range⟩ :=
      saturating_agrees_on_Ico cbtc pcd U hU_nn hU_pos hT_pos y hy_init hy_deriv_Ico
    -- Bound ‖y t‖ coordinatewise.
    show ‖sol'.trajectory t‖ ≤ M
    change ‖y t‖ ≤ M
    rw [pi_norm_le_iff_of_nonneg hM_pos.le]
    intro k
    refine Fin.lastCases ?_ (fun i => ?_) k
    · -- Last coord: |y_last t| ≤ U ≤ M.
      show ‖y t (Fin.last d)‖ ≤ M
      obtain ⟨h_lo, h_hi⟩ := h_range t ht_mem
      rw [Real.norm_eq_abs, abs_le]
      refine ⟨?_, ?_⟩
      · linarith
      · linarith
    · -- castSucc: y t i.castSucc = cbtc.sol.trajectory t i.
      show ‖y t i.castSucc‖ ≤ M
      have h_eq : y t i.castSucc = cbtc.sol.trajectory t i :=
        h_head_match t ht_mem i
      rw [h_eq]
      have h1 : ‖cbtc.sol.trajectory t i‖ ≤ ‖cbtc.sol.trajectory t‖ :=
        norm_le_pi_norm _ _
      have h2 : ‖cbtc.sol.trajectory t‖ ≤ M_cbtc := hM_cbtc_bd t ht
      linarith
  · -- Output range [0, U].
    intro σ hσ
    -- `(saturatingPIVP cbtc.pivp U).output = Fin.last d` by defn.
    show 0 ≤ sol'.trajectory σ (saturatingPIVP cbtc.pivp U).output ∧
      sol'.trajectory σ (saturatingPIVP cbtc.pivp U).output ≤ (U : ℝ)
    rw [saturatingPIVP_output]
    change 0 ≤ y σ (Fin.last d) ∧ y σ (Fin.last d) ≤ (U : ℝ)
    set T : ℝ := σ + 1 with hT_def
    have hT_pos : 0 < T := by linarith
    have hσ_mem : σ ∈ Set.Ico (0 : ℝ) T := ⟨hσ, by linarith⟩
    have hy_deriv_Ico : ∀ τ ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt y ((saturatingPIVP cbtc.pivp U).toPIVP.field (y τ)) τ := by
      intro τ hτ
      exact hy_deriv_all τ hτ.1
    obtain ⟨_, h_range⟩ :=
      saturating_agrees_on_Ico cbtc pcd U hU_nn hU_pos hT_pos y hy_init hy_deriv_Ico
    exact h_range σ hσ_mem
  · -- Head matching.
    intro σ hσ i
    set T : ℝ := σ + 1 with hT_def
    have hT_pos : 0 < T := by linarith
    have hσ_mem : σ ∈ Set.Ico (0 : ℝ) T := ⟨hσ, by linarith⟩
    have hy_deriv_Ico : ∀ τ ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt y ((saturatingPIVP cbtc.pivp U).toPIVP.field (y τ)) τ := by
      intro τ hτ
      exact hy_deriv_all τ hτ.1
    obtain ⟨h_head_match, _⟩ :=
      saturating_agrees_on_Ico cbtc pcd U hU_nn hU_pos hT_pos y hy_init hy_deriv_Ico
    show sol'.trajectory σ i.castSucc = cbtc.sol.trajectory σ i
    change y σ i.castSucc = cbtc.sol.trajectory σ i
    exact h_head_match σ hσ_mem i

/-! ## Step 5b: narrow analytic axiom + packaged convergence theorem.

The existence, boundedness, range, and head-matching of the surrogate
trajectory are all discharged by `saturating_extended_solution`
(Phase C+E). What remains is the *scalar convergence* of the tracker
coordinate `y(t)` to `α`. We isolate this single analytic fact as
a narrow axiom `saturating_tracker_tendsto`, and derive the full
packaged witness `saturating_tracker_solution` as a theorem.

**Analytic content of the narrow axiom.** Given the extended PIVP
solution `sol'` whose head coordinates equal `cbtc.sol.trajectory`
and whose last coordinate stays in `[0, U]`, the last coordinate
converges to `α` as `t → ∞`, with an effective modulus derivable
(in paper) via the `τ = ∫(U-y)` time rescaling and a Duhamel
solution of `dΦ/dτ = ε(t) - Φ`. See
`projects/Bounded/notes/saturating-surrogate-LPP.tex`,
Proposition "Convergence" (around line 124).

**Structure of the paper proof** (to be formalized in Lean).
Let `y(t) := sol'.trajectory t (Fin.last d)`,
`x(t) := cbtc.sol.trajectory t cbtc.pivp.output`,
`φ(t) := y(t) - α`, `ε(t) := x(t) - α`, `κ := U - α > 0`.

1. **ODE rewrite.** `y' = (x - y)(U - y)` rewrites as
   `φ' = (ε - φ)(U - y) = ε·(U-y) - φ·(U-y)`.
2. **τ-rescaling.** Define `G(t) := ∫₀^t (U - y(s)) ds`.
   Since `U - y ≥ 0` (from `_h_range`), `G` is nondecreasing.
   In the `τ`-variable (`Φ(τ) := φ(t(τ))`, `E(τ) := ε(t(τ))`),
   the ODE becomes `dΦ/dτ = E(τ) - Φ(τ)`.
3. **Duhamel formula.** `Φ(τ) = -α·e^{-τ} + ∫₀^τ e^{-(τ-σ)}·E(σ) dσ`.
4. **Bootstrap for `G → ∞`.** The nonlinear wrinkle: we need
   `τ(t) = G(t) → ∞` to translate τ-decay into t-decay. The paper
   argues (proof of Prop "Convergence"): if `G` stayed bounded,
   `y` would have to approach `U`, but `y = U` is an unstable
   equilibrium of `y' = (x-y)(U-y)` (since near `y=U`, `x ≈ α < U`
   gives `y' ≈ (α-U)(U-y) < 0`), pushing `y` away from `U`.
   Contradiction: `G` is unbounded.
5. **Quantitative modulus.** With `r₀ := ⌈log(2U/κ)⌉`,
   `T₀ := cbtc.modulus r₀`, splitting the Duhamel integral at
   `σ₀ := τ(T₀)` and using `|E| ≤ e^{-r₀} ≤ κ/(2U)` for `σ > σ₀`
   gives `|Φ(τ)| ≤ κ/2` for `τ > σ₀ + log(2U/κ) + 1`. Back in
   real time, `U - y ≥ κ/2` eventually, so `τ(t) ≥ (κ/2)·t + O(1)`,
   and the final bound is
   `μ'(r) ≤ cbtc.modulus(r + r₀) + κ⁻¹·log(2U/κ) + 1`.

**Why this is axiomatized rather than proved.** Formalizing
steps 2-5 in Lean 4 requires:

  * `G` defined via `intervalIntegral` with `y` continuous
    (available from `HasDerivAt`);
  * a time-dependent change-of-variables for ODEs (not directly
    in Mathlib; would need to be built on
    `MeasureTheory.Integral.SetIntegral`);
  * a τ-domain Grönwall with time-varying forcing `E(τ)`
    (Mathlib's `gronwallBound` assumes constant `ε`);
  * the `G → ∞` bootstrap via instability of `y = U` (an
    ad hoc lemma specific to this ODE, ~200-300 lines).

Total estimated effort: 800-1500 lines of Mathlib-style analysis.
This is deferred as the sole remaining analytic axiom. All
*structural* content (ODE existence on `[0, ∞)`, forward-invariance
of `[0, U]`, head-matching with the driver, PCD non-negativity,
quadraticization-readiness) is proved, not axiomatized.

We axiomatize the quantitative modulus directly rather than going
through `Tendsto`, to preserve exact parity with the
`CertifiedBoundedTimeComputable.convergence` signature consumed
downstream. -/

/-- **Narrow analytic axiom.** Given an extended saturating solution
`sol'` whose head coordinates match the driver `cbtc.sol.trajectory`
and whose last coordinate stays in `[0, U]` with `α < U < 1`, the
tracker coordinate `sol'.trajectory t (Fin.last d)` converges to
`α` with an effective modulus `μ'`.

This is the sole piece of analytic content deferred: existence,
boundedness, output range, and head-matching are *proved*
(see `saturating_extended_solution`). See the section header for a
detailed breakdown of the paper proof and the Mathlib gaps that
would need to be closed to discharge this axiom.

The `_h_head` hypothesis is currently unused in the conclusion
(which mentions only the last coordinate) but is supplied by the
caller from the structural witness; kept as a positional parameter
so a future proof can exploit it if the argument needs head-time
coupling. Same for `_h_range`: the `0 ≤ y ≤ U` invariance is the
key fact used in the τ-rescaling argument. -/
axiom saturating_tracker_tendsto {d : ℕ} {α : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d α)
    (U : ℚ) (hα_nn : 0 ≤ α) (hU_lo : α < (U : ℝ)) (hU_hi : (U : ℝ) < 1)
    (sol' : PIVP.Solution (saturatingPIVP cbtc.pivp U).toPIVP)
    (_h_range : ∀ σ : ℝ, 0 ≤ σ →
      0 ≤ sol'.trajectory σ (saturatingPIVP cbtc.pivp U).output ∧
      sol'.trajectory σ (saturatingPIVP cbtc.pivp U).output ≤ (U : ℝ))
    (_h_head : ∀ σ : ℝ, 0 ≤ σ → ∀ i : Fin d,
      sol'.trajectory σ i.castSucc = cbtc.sol.trajectory σ i) :
    ∃ (μ' : TimeModulus), ∀ r : ℕ, ∀ t : ℝ, t > μ' r →
      |sol'.trajectory t (saturatingPIVP cbtc.pivp U).output - α|
        < Real.exp (-(r : ℝ))

/-- **Phase D (packaged).** Convergence of the saturating tracker
`y` to `α`, together with boundedness and output range.

**Proved content:** existence of `sol'`, boundedness of the full
vector trajectory, output coordinate ∈ `[0, U]`, all from
`saturating_extended_solution`. **Narrow analytic input:** scalar
convergence modulus, via `saturating_tracker_tendsto`. -/
theorem saturating_tracker_convergence {d : ℕ} {α : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d α)
    (pcd : PolyCRNDecomposition d cbtc.pivp)
    (U : ℚ) (hα_nn : 0 ≤ α) (hU_lo : α < (U : ℝ)) (hU_hi : (U : ℝ) < 1) :
    ∃ (sol' : PIVP.Solution (saturatingPIVP cbtc.pivp U).toPIVP)
      (μ' : TimeModulus),
      (∀ r : ℕ, ∀ t : ℝ, t > μ' r →
        |sol'.trajectory t (saturatingPIVP cbtc.pivp U).output - α|
          < Real.exp (-(r : ℝ))) ∧
      (saturatingPIVP cbtc.pivp U).toPIVP.IsBounded sol'.trajectory ∧
      (∀ σ : ℝ, 0 ≤ σ →
        0 ≤ sol'.trajectory σ (saturatingPIVP cbtc.pivp U).output ∧
        sol'.trajectory σ (saturatingPIVP cbtc.pivp U).output ≤ (U : ℝ)) := by
  have hU_nn : (0 : ℝ) ≤ (U : ℝ) := le_trans hα_nn hU_lo.le
  have hU_pos : (0 : ℝ) < (U : ℝ) := lt_of_le_of_lt hα_nn hU_lo
  obtain ⟨sol', h_bounded, h_range, h_head⟩ :=
    saturating_extended_solution cbtc pcd U hU_nn hU_pos
  obtain ⟨μ', h_conv⟩ :=
    saturating_tracker_tendsto cbtc U hα_nn hU_lo hU_hi sol' h_range h_head
  exact ⟨sol', μ', h_conv, h_bounded, h_range⟩

/-- Residual witness: the extended PIVP has a certified bounded-time
computation for `α` (the same target), whose output trajectory stays
in `[0, U]` on `t ≥ 0`. This is now a **theorem** proved by
`saturating_tracker_convergence`, which discharges existence,
boundedness, and range from `saturating_extended_solution` and
uses the narrow axiom `saturating_tracker_tendsto` only for scalar
convergence. -/
theorem saturating_tracker_solution {d : ℕ} {α : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d α)
    (pcd : PolyCRNDecomposition d cbtc.pivp)
    (U : ℚ) (hα_nn : 0 ≤ α) (hU_lo : α < (U : ℝ)) (hU_hi : (U : ℝ) < 1) :
    ∃ (sol' : PIVP.Solution (saturatingPIVP cbtc.pivp U).toPIVP)
      (μ' : TimeModulus),
      (∀ r : ℕ, ∀ t : ℝ, t > μ' r →
        |sol'.trajectory t (saturatingPIVP cbtc.pivp U).output - α|
          < Real.exp (-(r : ℝ))) ∧
      (saturatingPIVP cbtc.pivp U).toPIVP.IsBounded sol'.trajectory ∧
      (∀ σ, 0 ≤ σ →
        0 ≤ sol'.trajectory σ (saturatingPIVP cbtc.pivp U).output ∧
        sol'.trajectory σ (saturatingPIVP cbtc.pivp U).output ≤ (U : ℝ)) :=
  saturating_tracker_convergence cbtc pcd U hα_nn hU_lo hU_hi

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
    saturating_tracker_solution cbtc pcd U hα_nn hU_lo hU_hi
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
