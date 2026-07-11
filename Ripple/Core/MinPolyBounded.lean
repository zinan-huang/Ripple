/-
  Ripple.Core.MinPolyBounded — a priori bounds for the min-polynomial PIVP.

  The algebraic single-species PIVP (see `Ripple.LPP.AlgebraicConstruction`)

      dx/dt = P(x),    x(0) = 0

  where `α > 0` is the smallest positive root of an integer polynomial
  `P` with `P.coeff 0 ≥ 0`, admits a bounded-global solution. The two
  bounds are:

    • Lower bound  `y(t) ≥ 0`  — derived from the `crn_local_nonneg`
      machinery (minPolyPIVP has a non-negative-coefficient
      decomposition).

    • Upper bound  `y(t) ≤ α`  — first-exit-time topological argument:
      the constant `![α]` is a solution, and if `y` ever reaches `α`,
      ODE uniqueness forces `y ≡ ![α]` beyond that point.

  The two bounds together give `‖y(t)‖ ≤ α` on every local-solution
  half-open interval `Ico 0 T`, and `locally_lipschitz_bounded_global_ode_proved`
  then lifts any putative local solution to a global one.
-/

import Ripple.LPP.MinPolyData
import Ripple.Core.ODEShifted
import Ripple.Core.ZeroInitPositivity

open Set Filter Topology

namespace Ripple
namespace Algebraic

open MvPolynomial

/-! ## minPolyPIVP as a PolyPIVP with a PolyCRNDecomposition -/

/-- The PolyCRNDecomposition for `minPolyPIVP P` under `0 ≤ P.coeff 0`. -/
noncomputable def minPolyPIVP_pcd (P : Polynomial ℤ)
    (hc0_nonneg : 0 ≤ P.coeff 0) :
    PolyCRNDecomposition 1 (minPolyPIVP P) where
  prod := fun _ => minPolyProd P
  degr := fun _ => minPolyDegr P
  prod_nonneg := fun _ => minPolyProd_coeff_nonneg P
  degr_nonneg := fun _ => minPolyDegr_coeff_nonneg P
  init_nonneg := fun _ => by simp [minPolyPIVP]
  field_eq := fun i => by
    change (minPolyPIVP P).field i = minPolyProd P - minPolyDegr P * X i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    change minPolyField P = minPolyProd P - minPolyDegr P * X 0
    exact minPolyField_eq_decomp P hc0_nonneg

/-! ## Evaluation of the min-poly field at a state -/

/-- The field of `minPolyPIVP P`, evaluated at a real state `x : Fin 1 → ℝ`,
equals `Polynomial.aeval (x 0) P` over ℝ. -/
lemma minPolyPIVP_field_eq_aeval (P : Polynomial ℤ) (x : Fin 1 → ℝ) (i : Fin 1) :
    (minPolyPIVP P).toPIVP.field x i = (Polynomial.aeval (x 0) P : ℝ) := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  show (minPolyField P).eval₂ (Rat.castHom ℝ) x = _
  rw [minPolyField_eval]
  rw [Polynomial.aeval_eq_sum_range (p := P) (x := x 0)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [Algebra.smul_def, eq_intCast]

/-- The constant state `(fun _ => α)` with `aeval α P = 0` is a zero of the field. -/
lemma minPolyPIVP_field_at_alpha {α : ℝ} {P : Polynomial ℤ}
    (hα_root : (Polynomial.aeval α P : ℝ) = 0) (i : Fin 1) :
    (minPolyPIVP P).toPIVP.field (fun _ => α) i = 0 := by
  rw [minPolyPIVP_field_eq_aeval P (fun _ => α) i, hα_root]

/-! ## Sup-norm on Fin 1 → ℝ -/

/-- `‖v‖ = |v 0|` for `v : Fin 1 → ℝ` under the sup norm. -/
lemma norm_fin_one (v : Fin 1 → ℝ) : ‖v‖ = |v 0| := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (abs_nonneg _)]
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rfl
  · have := norm_le_pi_norm v 0
    rwa [Real.norm_eq_abs] at this

/-! ## Constant `α`-solution -/

/-- The constant function `s ↦ (fun _ => α)` is a solution of `minPolyPIVP P`
as `HasDerivWithinAt` for any set, whenever `α` is a real root of `P`. -/
lemma const_alpha_hasDerivWithinAt {α : ℝ} {P : Polynomial ℤ}
    (hα_root : (Polynomial.aeval α P : ℝ) = 0) (s : Set ℝ) (t : ℝ) :
    HasDerivWithinAt (fun _ : ℝ => (fun _ : Fin 1 => α))
      ((minPolyPIVP P).toPIVP.field (fun _ => α)) s t := by
  have h0 : (minPolyPIVP P).toPIVP.field (fun _ : Fin 1 => α) = (fun _ => (0 : ℝ)) := by
    funext i
    exact minPolyPIVP_field_at_alpha hα_root i
  rw [h0]
  exact (hasDerivAt_const _ _).hasDerivWithinAt

/-- Constant `α` global-HasDerivAt version. -/
lemma const_alpha_hasDerivAt {α : ℝ} {P : Polynomial ℤ}
    (hα_root : (Polynomial.aeval α P : ℝ) = 0) (t : ℝ) :
    HasDerivAt (fun _ : ℝ => (fun _ : Fin 1 => α))
      ((minPolyPIVP P).toPIVP.field (fun _ => α)) t := by
  have h0 : (minPolyPIVP P).toPIVP.field (fun _ : Fin 1 => α) = (fun _ => (0 : ℝ)) := by
    funext i
    exact minPolyPIVP_field_at_alpha hα_root i
  rw [h0]
  exact hasDerivAt_const _ _

/-! ## Lower-bound invariance -/

/-- Lower bound: any local solution of `minPolyPIVP P` starting at 0 stays
non-negative on `Ico 0 T`. -/
lemma minPolyPIVP_local_nonneg
    (P : Polynomial ℤ) (hc0_nonneg : 0 ≤ P.coeff 0)
    (T : ℝ) (hT : 0 < T) (y : ℝ → Fin 1 → ℝ)
    (hy0 : y 0 = fun _ => (0 : ℝ))
    (h_ode : ∀ t ∈ Ico (0 : ℝ) T,
      HasDerivAt y ((minPolyPIVP P).toPIVP.field (y t)) t) :
    ∀ t ∈ Ico (0 : ℝ) T, ∀ i, 0 ≤ y t i := by
  have h_crn : IsCRNImplementable 1 (minPolyPIVP P).toPIVP.field :=
    (minPolyPIVP_pcd P hc0_nonneg).toIsCRNImplementable
  have h_lip := polyPIVP_field_locally_lipschitz (minPolyPIVP P)
  have h_init_nn : ∀ i, 0 ≤ y 0 i := by
    intro i
    rw [hy0]
  exact fun t ht i => crn_local_nonneg h_crn h_lip T hT y h_init_nn h_ode t ht i

/-! ## Upper-bound invariance via first-exit-time -/

/-- Upper bound: any local solution of `minPolyPIVP P` starting at 0 stays
`≤ α` on `Ico 0 T`. -/
lemma minPolyPIVP_local_upper_bound
    {α : ℝ} {P : Polynomial ℤ}
    (hα_pos : 0 < α)
    (hα_root : (Polynomial.aeval α P : ℝ) = 0)
    (T : ℝ) (_hT : 0 < T) (y : ℝ → Fin 1 → ℝ)
    (hy0 : y 0 = fun _ => (0 : ℝ))
    (h_ode : ∀ t ∈ Ico (0 : ℝ) T,
      HasDerivAt y ((minPolyPIVP P).toPIVP.field (y t)) t)
    (h_nn : ∀ t ∈ Ico (0 : ℝ) T, 0 ≤ y t 0) :
    ∀ t ∈ Ico (0 : ℝ) T, y t 0 ≤ α := by
  classical
  by_contra h_not
  push Not at h_not
  obtain ⟨t₀, ht₀, ht₀_gt⟩ := h_not
  -- y(0) 0 = 0 < α < y(t₀) 0
  have hy00 : y 0 0 = 0 := by rw [hy0]
  have ht₀_pos : 0 < t₀ := by
    rcases eq_or_lt_of_le ht₀.1 with h0 | hp
    · rw [← h0] at ht₀_gt; rw [hy00] at ht₀_gt; linarith
    · exact hp
  -- Continuity setup
  have hy_contAt : ∀ s ∈ Ico (0 : ℝ) T, ContinuousAt y s := fun s hs =>
    (h_ode s hs).continuousAt
  have hy0_contAt : ∀ s ∈ Ico (0 : ℝ) T, ContinuousAt (fun s => y s 0) s := by
    intro s hs
    exact (continuous_apply (0 : Fin 1)).continuousAt.comp (hy_contAt s hs)
  have hy0_contOn : ContinuousOn (fun s => y s 0) (Icc (0 : ℝ) t₀) := by
    intro s hs
    have hs' : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_of_le_of_lt hs.2 ht₀.2⟩
    exact (hy0_contAt s hs').continuousWithinAt
  -- IVT: α ∈ image of y·0 on [0, t₀]
  have hIVT : Set.Icc (y 0 0) (y t₀ 0) ⊆ (fun s => y s 0) '' Set.Icc 0 t₀ :=
    intermediate_value_Icc ht₀_pos.le hy0_contOn
  have hα_in : α ∈ Set.Icc (y 0 0) (y t₀ 0) := by
    rw [hy00]; exact ⟨hα_pos.le, ht₀_gt.le⟩
  obtain ⟨s_touch, hs_touch_Icc, hs_touch_eq⟩ := hIVT hα_in
  -- Set of touch times on [0, t₀]
  set S : Set ℝ := {s | s ∈ Icc (0 : ℝ) t₀ ∧ y s 0 = α} with hS_def
  have hS_nonempty : S.Nonempty := ⟨s_touch, hs_touch_Icc, hs_touch_eq⟩
  have hS_bdd_above : BddAbove S := ⟨t₀, fun s hs => hs.1.2⟩
  have hS_closed : IsClosed S := by
    have h_preim : IsClosed (Icc (0 : ℝ) t₀ ∩ (fun s => y s 0) ⁻¹' {α}) :=
      ContinuousOn.preimage_isClosed_of_isClosed hy0_contOn isClosed_Icc isClosed_singleton
    convert h_preim using 1
  -- s₁ = sSup S ∈ S
  set s₁ : ℝ := sSup S with hs₁_def
  have hs₁_mem : s₁ ∈ S := hS_closed.csSup_mem hS_nonempty hS_bdd_above
  have hs₁_upper : ∀ s ∈ S, s ≤ s₁ := fun s hs => le_csSup hS_bdd_above hs
  have hs₁_Icc : s₁ ∈ Icc (0 : ℝ) t₀ := hs₁_mem.1
  have hs₁_eq : y s₁ 0 = α := hs₁_mem.2
  -- s₁ < t₀
  have hs₁_lt_t₀ : s₁ < t₀ := by
    rcases lt_or_eq_of_le hs₁_Icc.2 with h | h
    · exact h
    · exfalso; rw [← h, hs₁_eq] at ht₀_gt; linarith
  -- On Ioc s₁ t₀, y s 0 > α (strict).
  have h_above : ∀ s ∈ Ioc s₁ t₀, α < y s 0 := by
    intro s hs
    have hs_Icc : s ∈ Icc (0 : ℝ) t₀ :=
      ⟨le_trans hs₁_Icc.1 hs.1.le, hs.2⟩
    by_contra h_not_gt
    push Not at h_not_gt
    rcases lt_or_eq_of_le h_not_gt with h_lt | h_eq
    · have hy0_contOn_st : ContinuousOn (fun u => y u 0) (Icc s t₀) :=
        hy0_contOn.mono (fun u hu => ⟨le_trans hs_Icc.1 hu.1, hu.2⟩)
      have hIVT2 : Set.Icc (y s 0) (y t₀ 0)
          ⊆ (fun u => y u 0) '' Set.Icc s t₀ :=
        intermediate_value_Icc hs.2 hy0_contOn_st
      have hα_in2 : α ∈ Set.Icc (y s 0) (y t₀ 0) := ⟨h_lt.le, ht₀_gt.le⟩
      obtain ⟨s', hs'_Icc, hs'_eq⟩ := hIVT2 hα_in2
      have hs'_in_Icc_0 : s' ∈ Icc (0 : ℝ) t₀ :=
        ⟨le_trans hs_Icc.1 hs'_Icc.1, hs'_Icc.2⟩
      have hs'_S : s' ∈ S := ⟨hs'_in_Icc_0, hs'_eq⟩
      have hs'_le_s₁ : s' ≤ s₁ := hs₁_upper s' hs'_S
      have hs'_gt_s₁ : s' > s₁ := lt_of_lt_of_le hs.1 hs'_Icc.1
      linarith
    · -- y s 0 = α (via h_eq : y s 0 = α)
      have hs_S : s ∈ S := ⟨hs_Icc, h_eq⟩
      have h_le := hs₁_upper s hs_S
      linarith [hs.1]
  -- Pick δ > 0 such that for all s ∈ (s₁ - δ, s₁ + δ), |y s 0 - α| < 1.
  have h_s₁_in_Ico : s₁ ∈ Ico (0 : ℝ) T :=
    ⟨hs₁_Icc.1, lt_of_le_of_lt hs₁_Icc.2 ht₀.2⟩
  have h_cont_s₁ : ContinuousAt (fun s => y s 0) s₁ := hy0_contAt s₁ h_s₁_in_Ico
  have h_tendsto : Filter.Tendsto (fun s => y s 0) (𝓝 s₁) (𝓝 α) := by
    rw [← hs₁_eq]; exact h_cont_s₁
  -- We need an open ball around s₁ on which y · 0 < α + 1 uniformly.
  have h_ball_y : ∀ᶠ s in 𝓝 s₁, y s 0 < α + 1 := by
    have h_ev := h_tendsto.eventually_lt_const (show α < α + 1 by linarith)
    -- h_ev : ∀ᶠ s in 𝓝 s₁, y s 0 < α + 1
    exact h_ev
  -- Extract a metric ball
  obtain ⟨δ, hδ_pos, hδ_ball⟩ := Metric.mem_nhds_iff.mp h_ball_y
  -- hδ_ball : Metric.ball s₁ δ ⊆ {s | y s 0 < α + 1}
  -- Pick s_ε ∈ (s₁, min (s₁+δ) t₀).
  set s_ε : ℝ := s₁ + (min δ (t₀ - s₁)) / 2 with hs_ε_def
  have h_diff_pos : 0 < min δ (t₀ - s₁) := lt_min hδ_pos (by linarith)
  have hs_ε_gt : s₁ < s_ε := by
    change s₁ < s₁ + (min δ (t₀ - s₁)) / 2
    linarith
  have h_min_le_δ : min δ (t₀ - s₁) ≤ δ := min_le_left _ _
  have h_min_le_t : min δ (t₀ - s₁) ≤ t₀ - s₁ := min_le_right _ _
  have hs_ε_lt_t₀ : s_ε < t₀ := by
    change s₁ + (min δ (t₀ - s₁)) / 2 < t₀
    have : (min δ (t₀ - s₁)) / 2 < t₀ - s₁ := by
      have : (min δ (t₀ - s₁)) / 2 ≤ (t₀ - s₁) / 2 := by
        exact div_le_div_of_nonneg_right h_min_le_t (by norm_num)
      have h_half : (t₀ - s₁) / 2 < t₀ - s₁ := by linarith
      linarith
    linarith
  have hs_ε_lt_s₁δ : s_ε < s₁ + δ := by
    change s₁ + (min δ (t₀ - s₁)) / 2 < s₁ + δ
    have h_half : (min δ (t₀ - s₁)) / 2 ≤ δ / 2 := by
      exact div_le_div_of_nonneg_right h_min_le_δ (by norm_num)
    have h_half_lt : δ / 2 < δ := by linarith
    linarith
  -- Every u ∈ Icc s₁ s_ε lies in Metric.ball s₁ δ.
  have h_Icc_in_ball : ∀ u ∈ Icc s₁ s_ε, u ∈ Metric.ball s₁ δ := by
    intro u hu
    rw [Metric.mem_ball, Real.dist_eq]
    have h_diff : u - s₁ ≥ 0 := by linarith [hu.1]
    rw [abs_of_nonneg h_diff]
    have : u ≤ s_ε := hu.2
    linarith
  -- So y u 0 < α + 1 for all u ∈ Icc s₁ s_ε.
  have hy_lt_α1 : ∀ u ∈ Icc s₁ s_ε, y u 0 < α + 1 := fun u hu =>
    hδ_ball (h_Icc_in_ball u hu)
  -- Now apply shifted ODE uniqueness on Icc s₁ s_ε with M = α + 1.
  have hs_ε_Icc_0 : s_ε ∈ Icc (0 : ℝ) t₀ :=
    ⟨le_trans hs₁_Icc.1 hs_ε_gt.le, hs_ε_lt_t₀.le⟩
  have hIcc_sub : Icc s₁ s_ε ⊆ Ico (0 : ℝ) T := by
    intro u hu
    refine ⟨le_trans hs₁_Icc.1 hu.1, ?_⟩
    exact lt_of_le_of_lt (le_trans hu.2 hs_ε_lt_t₀.le) ht₀.2
  -- Derivatives on Icc s₁ s_ε
  have hy_deriv : ∀ u ∈ Icc s₁ s_ε,
      HasDerivWithinAt y ((minPolyPIVP P).toPIVP.field (y u)) (Icc s₁ s_ε) u :=
    fun u hu => (h_ode u (hIcc_sub hu)).hasDerivWithinAt
  have hconst_deriv : ∀ u ∈ Icc s₁ s_ε,
      HasDerivWithinAt (fun _ : ℝ => (fun _ : Fin 1 => α))
        ((minPolyPIVP P).toPIVP.field (fun _ : Fin 1 => α)) (Icc s₁ s_ε) u :=
    fun u _ => const_alpha_hasDerivWithinAt hα_root (Icc s₁ s_ε) u
  -- y s₁ = fun _ => α
  have hy_s₁ : y s₁ = (fun _ : Fin 1 => α) := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact hs₁_eq
  -- Norm bounds on Icc s₁ s_ε
  have hM_nn : 0 ≤ α + 1 := by linarith
  have hy_bound : ∀ u ∈ Icc s₁ s_ε, ‖y u‖ ≤ α + 1 := by
    intro u hu
    have hu_Ico : u ∈ Ico (0 : ℝ) T := hIcc_sub hu
    have h_u_0_nn : 0 ≤ y u 0 := h_nn u hu_Ico
    have h_u_0_lt : y u 0 < α + 1 := hy_lt_α1 u hu
    rw [norm_fin_one, abs_of_nonneg h_u_0_nn]
    linarith
  have hconst_bound : ∀ u ∈ Icc s₁ s_ε, ‖(fun _ : Fin 1 => α)‖ ≤ α + 1 := by
    intro u _
    rw [norm_fin_one, abs_of_pos hα_pos]
    linarith
  have h_lip := polyPIVP_field_locally_lipschitz (minPolyPIVP P)
  -- Apply shifted uniqueness
  have h_eq_on := solutions_agree_on_Icc_shifted
    (M := α + 1) (s₀ := s₁) (T := s_ε) hs_ε_gt hM_nn h_lip
    hy_s₁ hy_deriv hconst_deriv hy_bound hconst_bound
  -- y s_ε = fun _ => α
  have hy_s_ε : y s_ε = (fun _ : Fin 1 => α) :=
    h_eq_on (right_mem_Icc.mpr hs_ε_gt.le)
  -- Thus y s_ε 0 = α, contradicting h_above
  have hs_ε_Ioc : s_ε ∈ Ioc s₁ t₀ := ⟨hs_ε_gt, hs_ε_lt_t₀.le⟩
  have hy_s_ε_eq_α : y s_ε 0 = α := by rw [hy_s_ε]
  have := h_above s_ε hs_ε_Ioc
  linarith [hy_s_ε_eq_α]

/-! ## Combined bound: ‖y(t)‖ ≤ α -/

/-- Combined: any local solution has `‖y(t)‖ ≤ α` on `Ico 0 T`. -/
lemma minPolyPIVP_local_norm_bound
    {α : ℝ} {P : Polynomial ℤ}
    (hα_pos : 0 < α)
    (hα_root : (Polynomial.aeval α P : ℝ) = 0)
    (hc0_nonneg : 0 ≤ P.coeff 0)
    (T : ℝ) (hT : 0 < T) (y : ℝ → Fin 1 → ℝ)
    (hy0 : y 0 = fun _ => (0 : ℝ))
    (h_ode : ∀ t ∈ Ico (0 : ℝ) T,
      HasDerivAt y ((minPolyPIVP P).toPIVP.field (y t)) t) :
    ∀ t ∈ Ico (0 : ℝ) T, ‖y t‖ ≤ α := by
  intro t ht
  have h_nn_all := minPolyPIVP_local_nonneg P hc0_nonneg T hT y hy0 h_ode
  have h_nn_0 : ∀ t ∈ Ico (0 : ℝ) T, 0 ≤ y t 0 := fun t ht => h_nn_all t ht 0
  have h_ub := minPolyPIVP_local_upper_bound hα_pos hα_root T hT y hy0 h_ode h_nn_0
  rw [norm_fin_one]
  rw [abs_of_nonneg (h_nn_0 t ht)]
  exact h_ub t ht

/-! ## Assembled global existence -/

/-- Global solution existence for the min-poly PIVP **with continuity**: same
content as `minPolyPIVP_global_solution` but additionally surfaces a global
`Continuous sol.trajectory` witness. Built on
`locally_lipschitz_bounded_global_ode_proved_continuous`. -/
noncomputable def minPolyPIVP_global_solution_continuous
    {α : ℝ} {P : Polynomial ℤ}
    (hα_pos : 0 < α)
    (hα_root : (Polynomial.aeval α P : ℝ) = 0)
    (hc0_nonneg : 0 ≤ P.coeff 0) :
    Σ' (sol : PIVP.Solution (minPolyPIVP P).toPIVP), Continuous sol.trajectory := by
  by_cases h_c0 : P.coeff 0 = 0
  · -- c₀ = 0: trajectory y = (fun _ _ => 0) is a solution
    refine ⟨{
      trajectory := fun _ _ => 0
      init_cond := ?_
      is_solution := ?_ }, ?_⟩
    · funext i
      simp [minPolyPIVP, PolyPIVP.toPIVP]
    · intro t _
      -- Show field(0) = 0: aeval 0 P = P.coeff 0 = 0
      have h_field : (minPolyPIVP P).toPIVP.field (fun _ : Fin 1 => (0 : ℝ))
          = fun _ => 0 := by
        funext i
        rw [minPolyPIVP_field_eq_aeval P (fun _ => 0) i]
        have : (Polynomial.aeval (0 : ℝ) P : ℝ) = (P.coeff 0 : ℝ) := by
          simp [Polynomial.aeval_def, Polynomial.eval₂_at_zero, eq_intCast]
        rw [this, h_c0]; simp
      rw [h_field]
      exact hasDerivAt_const t (fun _ : Fin 1 => (0 : ℝ))
    · -- Continuous (fun _ => fun _ => 0).
      exact continuous_const
  · -- c₀ > 0 (we have c₀ ≥ 0 and c₀ ≠ 0)
    have hc0_pos : 0 < P.coeff 0 := lt_of_le_of_ne hc0_nonneg (Ne.symm h_c0)
    -- Apply global existence (continuous variant).
    have h_lip := polyPIVP_field_locally_lipschitz (minPolyPIVP P)
    have h_init_eq : (minPolyPIVP P).toPIVP.init = (fun _ : Fin 1 => (0 : ℝ)) := by
      funext i; simp [minPolyPIVP, PolyPIVP.toPIVP]
    have h_invariant : ∀ (T : ℝ), 0 < T → ∀ (y : ℝ → Fin 1 → ℝ),
        y 0 = (minPolyPIVP P).toPIVP.init →
        (∀ t ∈ Ico (0 : ℝ) T,
          HasDerivAt y ((minPolyPIVP P).toPIVP.field (y t)) t) →
        ∀ t ∈ Ico (0 : ℝ) T, ‖y t‖ ≤ α := by
      intro T hT y hy0_init h_ode t ht
      have hy0 : y 0 = fun _ : Fin 1 => (0 : ℝ) := by
        rw [hy0_init, h_init_eq]
      exact minPolyPIVP_local_norm_bound hα_pos hα_root hc0_nonneg T hT y hy0 h_ode t ht
    have h_ex := locally_lipschitz_bounded_global_ode_proved_continuous
      (minPolyPIVP P).toPIVP.field (minPolyPIVP P).toPIVP.init h_lip
      α hα_pos h_invariant
    refine ⟨{
      trajectory := Classical.choose h_ex
      init_cond := (Classical.choose_spec h_ex).1
      is_solution := (Classical.choose_spec h_ex).2.1
    }, (Classical.choose_spec h_ex).2.2⟩

/-- Global solution existence for the min-poly PIVP: the statement formerly
axiomatized as `minPolyPIVP_exists_solution`. -/
noncomputable def minPolyPIVP_global_solution
    {α : ℝ} {P : Polynomial ℤ}
    (hα_pos : 0 < α)
    (hα_root : (Polynomial.aeval α P : ℝ) = 0)
    (hc0_nonneg : 0 ≤ P.coeff 0) :
    PIVP.Solution (minPolyPIVP P).toPIVP :=
  (minPolyPIVP_global_solution_continuous hα_pos hα_root hc0_nonneg).1

/-- Continuity of the min-poly global solution trajectory. -/
lemma minPolyPIVP_global_solution_continuous_traj
    {α : ℝ} {P : Polynomial ℤ}
    (hα_pos : 0 < α)
    (hα_root : (Polynomial.aeval α P : ℝ) = 0)
    (hc0_nonneg : 0 ≤ P.coeff 0) :
    Continuous (minPolyPIVP_global_solution hα_pos hα_root hc0_nonneg).trajectory :=
  (minPolyPIVP_global_solution_continuous hα_pos hα_root hc0_nonneg).2

end Algebraic
end Ripple
