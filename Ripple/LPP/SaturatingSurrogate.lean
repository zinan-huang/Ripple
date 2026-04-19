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
