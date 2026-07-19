import Ripple.Number.Frobenius.F5BridgeCore
import Ripple.Number.Frobenius.AperyG2BoundedNearConifold
import Ripple.Number.Frobenius.AperyACoefficientSharpLower

namespace Ripple.Number

/-- C9 step d: connection-coefficient extraction for the differentiated numerator.

Given `AperyFrobeniusConnectionCoefficientIdentification` (the hypothesis that the
Frobenius branches are concretely identified with the ordinary Apéry series), proves:

1. the `ρ = 1/2` singular coefficient cancels in
   `aperyF5GFBSecondReal - ζ(3) * aperyF5GFASecondReal`, so the differentiated
   numerator is bounded near `z₁` from the left; and
2. the `ρ = 1/2` coefficient of `aperyF5GFASecondReal` is nonzero with the
   correct sign, so `|z₁-z|^(3/2) * aperyF5GFASecondReal z` has a positive
   lower bound.

The hypothesis `_hconn` is discharged unconditionally by
`aperyRatioBound_step_c_connection_coefficients` in `F5BridgeCore.lean`. -/
theorem aperyF5_missing_connection_cancellation_and_denominator_lower
    (_hcoef : AperyFrobeniusRatioFamilyCoefficientControl)
    (_hbirk : AperyFrobeniusBirkhoffResidualSharpAsymptotics)
    (_hconn : AperyFrobeniusConnectionCoefficientIdentification) :
    AperyF5DifferentiatedNumeratorBoundedNearConifold ∧
      AperyF5GFASecondRealThreeHalvesLowerNearConifold := by
  exact ⟨aperyF5DifferentiatedNumeratorBoundedNearConifold_proven,
    aperyF5GFASecondReal_three_halves_lower_from_coefficients⟩

/-- C3 step d: transfer branch asymptotics and connection coefficients to
the differentiated analytic numerator `B'' - ζ(3)A''`. -/
theorem aperyRatioBound_step_d_series_to_differentiated_numerator
    (hcoef : AperyFrobeniusRatioFamilyCoefficientControl)
    (hbirk : AperyFrobeniusBirkhoffResidualSharpAsymptotics)
    (hconn : AperyFrobeniusConnectionCoefficientIdentification) :
    AperyF5DifferentiatedNumeratorThreeHalvesBound := by
  obtain ⟨hnum, hden⟩ :=
    aperyF5_missing_connection_cancellation_and_denominator_lower
      hcoef hbirk hconn
  exact
    aperyF5_differentiated_numerator_three_halves_of_bounded_and_denominator_lower
      hnum hden

/-- C3 step e: the numerator estimate implies the local `3/2` ratio bound
by dividing by the positive denominator `A''(z)`. -/
theorem aperyRatioBound_step_e_ratio_bound_of_numerator
    (hnum : AperyF5DifferentiatedNumeratorThreeHalvesBound) :
    AperyFrobeniusRatioBound := by
  rcases hnum with ⟨K, hK_pos, δ, hδ_pos, hbound⟩
  refine ⟨K, hK_pos, δ, hδ_pos, ?_⟩
  intro z hz_pos hz_lt hz_near
  have hA_pos : 0 < aperyF5GFASecondReal z :=
    aperyF5GFASecondReal_pos hz_pos hz_lt
  have hnum_bound := hbound z hz_pos hz_lt hz_near
  unfold aperyF5AnalyticRatio
  have hrewrite :
      aperyF5GFBSecondReal z / aperyF5GFASecondReal z - aperyZeta3Series =
        (aperyF5GFBSecondReal z - aperyZeta3Series * aperyF5GFASecondReal z) /
          aperyF5GFASecondReal z := by
    field_simp [hA_pos.ne']
  rw [hrewrite, abs_div, abs_of_pos hA_pos]
  rw [div_le_iff₀ hA_pos]
  exact hnum_bound

/-- Local conifold `3/2` estimate expected from the ratio-bound family,
Birkhoff sharp asymptotics, and connection-coefficient analysis. -/
theorem aperyFrobeniusRatioBound_from_ratio_family_and_birkhoff :
    AperyFrobeniusRatioBound := by
  have hcoef := aperyRatioBound_step_a_ratio_family_coefficient_control
  have hbirk := aperyRatioBound_step_b_birkhoff_residual_sharp_asymptotics hcoef
  have hconn := aperyRatioBound_step_c_connection_coefficients hbirk
  have hnum := aperyRatioBound_step_d_series_to_differentiated_numerator
    hcoef hbirk hconn
  exact aperyRatioBound_step_e_ratio_bound_of_numerator hnum

/-- Pure globalization: a local conifold `3/2` estimate plus boundedness
away from the conifold gives the full-disk globalized estimate. -/
theorem aperyFrobeniusRatioBoundGlobalized_of_local_and_preconifold
    (hlocal : AperyFrobeniusRatioBound)
    (hpre : AperyFrobeniusRatioPreconifoldBound) :
    AperyFrobeniusRatioBoundGlobalized := by
  rcases hlocal with ⟨K₀, hK₀_pos, δ, hδ_pos, hlocal_bound⟩
  have hz1_pos : 0 < aperyConifoldZ1 := by
    rw [aperyF5ConifoldZ1_eq_inv_R]
    positivity
  let η : ℝ := min (δ / 2) (aperyConifoldZ1 / 2)
  have hη_pos : 0 < η := by
    dsimp [η]
    exact lt_min (half_pos hδ_pos) (half_pos hz1_pos)
  have hη_lt_z1 : η < aperyConifoldZ1 := by
    dsimp [η]
    exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hz1_pos)
  have hη_le_δ : η ≤ δ := by
    dsimp [η]
    exact le_trans (min_le_left _ _) (by linarith)
  rcases hpre η hη_pos hη_lt_z1 with ⟨M, hM_pos, hM_bound⟩
  let K : ℝ := max K₀ (M / (η * Real.sqrt η)) + 1
  refine ⟨K, ?_, ?_⟩
  · have hfrac_nn : 0 ≤ M / (η * Real.sqrt η) := by positivity
    have hmax_nn : 0 ≤ max K₀ (M / (η * Real.sqrt η)) :=
      le_max_of_le_left hK₀_pos.le
    linarith
  intro z hz_pos hz_lt
  let d : ℝ := |aperyConifoldZ1 - z|
  have hd_eq : d = aperyConifoldZ1 - z := by
    dsimp [d]
    exact abs_of_nonneg (sub_nonneg.mpr hz_lt.le)
  have hd_pos : 0 < d := by
    rw [hd_eq]
    exact sub_pos.mpr hz_lt
  have hscale_nn : 0 ≤ d * Real.sqrt d :=
    mul_nonneg hd_pos.le (Real.sqrt_nonneg d)
  by_cases hnear : aperyConifoldZ1 - z < δ
  · have hK₀_le : K₀ ≤ K := by
      dsimp [K]
      linarith [le_max_left K₀ (M / (η * Real.sqrt η))]
    calc
      |aperyF5AnalyticRatio z - aperyZeta3Series|
          ≤ K₀ * d * Real.sqrt d := by
            simpa [d, hd_eq] using hlocal_bound z hz_pos hz_lt hnear
      _ ≤ K * d * Real.sqrt d := by
            nlinarith [mul_le_mul_of_nonneg_right hK₀_le hscale_nn]
      _ = K * |aperyConifoldZ1 - z| *
            Real.sqrt |aperyConifoldZ1 - z| := by
            simp [d, mul_assoc]
  · have hδ_le : δ ≤ aperyConifoldZ1 - z := le_of_not_gt hnear
    have hη_le_d : η ≤ d := by
      rw [hd_eq]
      exact le_trans hη_le_δ hδ_le
    have hsqrt_le : Real.sqrt η ≤ Real.sqrt d := Real.sqrt_le_sqrt hη_le_d
    have hη_scale_le : η * Real.sqrt η ≤ d * Real.sqrt d := by
      exact mul_le_mul hη_le_d hsqrt_le (Real.sqrt_nonneg η) hd_pos.le
    have hden_pos : 0 < η * Real.sqrt η :=
      mul_pos hη_pos (Real.sqrt_pos.mpr hη_pos)
    have hfrac_le : M / (η * Real.sqrt η) ≤ K := by
      dsimp [K]
      linarith [le_max_right K₀ (M / (η * Real.sqrt η))]
    have hfrac_nn : 0 ≤ M / (η * Real.sqrt η) :=
      div_nonneg hM_pos.le hden_pos.le
    calc
      |aperyF5AnalyticRatio z - aperyZeta3Series|
          ≤ M := hM_bound z hz_pos hz_lt (by simpa [hd_eq] using hη_le_d)
      _ = (M / (η * Real.sqrt η)) * (η * Real.sqrt η) := by
            field_simp [hden_pos.ne']
      _ ≤ (M / (η * Real.sqrt η)) * (d * Real.sqrt d) :=
            mul_le_mul_of_nonneg_left hη_scale_le hfrac_nn
      _ ≤ K * (d * Real.sqrt d) :=
            mul_le_mul_of_nonneg_right hfrac_le hscale_nn
      _ = K * |aperyConifoldZ1 - z| *
            Real.sqrt |aperyConifoldZ1 - z| := by
            simp [d, mul_assoc]

/-- C1 scaffold theorem: the globalized F5 Frobenius hypothesis is now
reduced to two named analytic sub-obligations:

* `aperyFrobeniusRatioBound_from_ratio_family_and_birkhoff`, the genuine
  conifold Frobenius/Birkhoff/connection-coefficient problem;
* `aperyFrobeniusRatioPreconifoldBound_from_series_continuity`, the
  ordinary compactness bound away from the conifold endpoint. -/
theorem aperyFrobeniusRatioBoundGlobalized_scaffold :
    AperyFrobeniusRatioBoundGlobalized := by
  exact aperyFrobeniusRatioBoundGlobalized_of_local_and_preconifold
    aperyFrobeniusRatioBound_from_ratio_family_and_birkhoff
    aperyFrobeniusRatioPreconifoldBound_from_series_continuity

/-- Globalized F5 immediately implies the local Frobenius F5 statement. -/
theorem aperyFrobeniusRatioBound_of_globalized
    (h : AperyFrobeniusRatioBoundGlobalized) :
    AperyFrobeniusRatioBound := by
  rcases h with ⟨K, hK, hbound⟩
  refine ⟨K, hK, 1, by norm_num, ?_⟩
  intro z hz_pos hz_lt _hz_near
  exact hbound z hz_pos hz_lt

/-- (F5-Connection) The PIVP `ρ` coordinate tracks the analytic
`B''/A''` ratio in the same `|z₁ - z|^(3/2)` scale.

An exponential tracking statement can be used to prove this after adding
the scalar F6 comparison and a compact-transient bound; this Prop records
the scale needed by the bridge itself. -/
def AperyPIVPRatioTracking
    (init : Fin 8 → ℚ)
    (sol : PIVP.Solution (apery8VarPolyPIVP init).toPIVP) : Prop :=
  ∃ K_track : ℝ, 0 < K_track ∧
    ∀ t : ℝ, 0 ≤ t →
      |sol.trajectory t aperyF5_iR -
          aperyF5AnalyticRatio (sol.trajectory t aperyF5_iZ)|
        ≤ K_track * |aperyConifoldZ1 - sol.trajectory t aperyF5_iZ| *
            Real.sqrt |aperyConifoldZ1 - sol.trajectory t aperyF5_iZ|

/-- Closed bridge under the globalized Frobenius statement.

This is the algebraic core of the split: the proof is only the triangle
inequality plus the two `3/2`-scale hypotheses. -/
theorem aperyConifoldThreeHalvesBound_of_global_split
    (init : Fin 8 → ℚ)
    (sol : PIVP.Solution (apery8VarPolyPIVP init).toPIVP)
    (hf : AperyFrobeniusRatioBoundGlobalized)
    (ht : AperyPIVPRatioTracking init sol)
    (hz_in_disk :
      ∀ τ : ℝ, 0 ≤ τ →
        0 < sol.trajectory τ aperyF5_iZ ∧
          sol.trajectory τ aperyF5_iZ < aperyConifoldZ1) :
    AperyConifoldThreeHalvesBound init sol := by
  rcases hf with ⟨K_frob, hK_frob, hf_bound⟩
  rcases ht with ⟨K_track, hK_track, ht_bound⟩
  refine ⟨K_track + K_frob, add_pos hK_track hK_frob, ?_⟩
  intro t ht_nonneg
  let zt : ℝ := sol.trajectory t aperyF5_iZ
  let d : ℝ := |aperyConifoldZ1 - zt| * Real.sqrt |aperyConifoldZ1 - zt|
  have hz := hz_in_disk t ht_nonneg
  have htrack :
      |sol.trajectory t aperyF5_iR - aperyF5AnalyticRatio zt|
        ≤ K_track * d := by
    simpa [zt, d, mul_assoc] using ht_bound t ht_nonneg
  have hfrob :
      |aperyF5AnalyticRatio zt - aperyZeta3Series|
        ≤ K_frob * d := by
    simpa [zt, d, mul_assoc] using hf_bound zt hz.1 hz.2
  have htri :
      |sol.trajectory t aperyF5_iR - aperyZeta3Series|
        ≤ |sol.trajectory t aperyF5_iR - aperyF5AnalyticRatio zt| +
          |aperyF5AnalyticRatio zt - aperyZeta3Series| :=
    abs_sub_le _ _ _
  calc
    |sol.trajectory t aperyF5_iR - aperyZeta3Series|
        ≤ |sol.trajectory t aperyF5_iR - aperyF5AnalyticRatio zt| +
            |aperyF5AnalyticRatio zt - aperyZeta3Series| := htri
    _ ≤ K_track * d + K_frob * d := add_le_add htrack hfrob
    _ = (K_track + K_frob) * d := by ring
    _ = (K_track + K_frob) *
          |aperyConifoldZ1 - sol.trajectory t aperyF5_iZ| *
          Real.sqrt |aperyConifoldZ1 - sol.trajectory t aperyF5_iZ| := by
        simp [d, zt, aperyF5_iZ, mul_assoc]

/-- Downstream exponential convergence from the two F5Bridge hypotheses.

This is the public wrapper used by later Apéry PIVP statements: first build
the `3/2`-order conifold estimate from the globalized Frobenius bound and
PIVP tracking, then feed it to the existing exponential-upgrade lemma. -/
theorem apery_three_halves_bound_exponential_via_F5Bridge
    (init : Fin 8 → ℚ)
    (sol : PIVP.Solution (apery8VarPolyPIVP init).toPIVP)
    (hz_exp : ∃ C lam : ℝ, 0 < C ∧ 0 < lam ∧
      ∀ t : ℝ, 0 ≤ t →
        |aperyConifoldZ1 - sol.trajectory t aperyF5_iZ|
          ≤ C * Real.exp (-(lam * t)))
    (hf : AperyFrobeniusRatioBoundGlobalized)
    (ht : AperyPIVPRatioTracking init sol)
    (hz_in_disk :
      ∀ τ : ℝ, 0 ≤ τ →
        0 < sol.trajectory τ aperyF5_iZ ∧
          sol.trajectory τ aperyF5_iZ < aperyConifoldZ1) :
    ∃ K κ : ℝ, 0 < K ∧ 0 < κ ∧
      ∀ t : ℝ, 0 ≤ t →
        |sol.trajectory t aperyF5_iR - aperyZeta3Series|
          ≤ K * Real.exp (-(κ * t)) := by
  have hthree : AperyConifoldThreeHalvesBound init sol :=
    aperyConifoldThreeHalvesBound_of_global_split init sol hf ht hz_in_disk
  simpa [aperyF5_iZ, aperyF5_iR, aperyZeta3Series] using
    apery_three_halves_bound_exponential init sol hz_exp hthree

/-- Frobenius ratio control restricted to one PIVP trajectory.  This is the
right target for the local-to-global upgrade: it avoids pretending that the
local Frobenius disk gives a global estimate for every `z ∈ (0, z₁)`, while
still being exactly what the trajectory-level F5 bridge needs. -/
def AperyFrobeniusRatioBoundAlong
    (init : Fin 8 → ℚ)
    (sol : PIVP.Solution (apery8VarPolyPIVP init).toPIVP) : Prop :=
  ∃ K_frob : ℝ, 0 < K_frob ∧
    ∀ t : ℝ, 0 ≤ t →
      |aperyF5AnalyticRatio (sol.trajectory t aperyF5_iZ) - aperyZeta3Series|
        ≤ K_frob * |aperyConifoldZ1 - sol.trajectory t aperyF5_iZ| *
            Real.sqrt |aperyConifoldZ1 - sol.trajectory t aperyF5_iZ|

/-- Closed bridge under an along-trajectory Frobenius estimate.

This is the same triangle-inequality argument as
`aperyConifoldThreeHalvesBound_of_global_split`, but it only asks for the
Frobenius bound along `z(t)`. -/
theorem aperyConifoldThreeHalvesBound_of_along_split
    (init : Fin 8 → ℚ)
    (sol : PIVP.Solution (apery8VarPolyPIVP init).toPIVP)
    (hf : AperyFrobeniusRatioBoundAlong init sol)
    (ht : AperyPIVPRatioTracking init sol) :
    AperyConifoldThreeHalvesBound init sol := by
  rcases hf with ⟨K_frob, hK_frob, hf_bound⟩
  rcases ht with ⟨K_track, hK_track, ht_bound⟩
  refine ⟨K_track + K_frob, add_pos hK_track hK_frob, ?_⟩
  intro t ht_nonneg
  let zt : ℝ := sol.trajectory t aperyF5_iZ
  let d : ℝ := |aperyConifoldZ1 - zt| * Real.sqrt |aperyConifoldZ1 - zt|
  have htrack :
      |sol.trajectory t aperyF5_iR - aperyF5AnalyticRatio zt|
        ≤ K_track * d := by
    simpa [zt, d, mul_assoc] using ht_bound t ht_nonneg
  have hfrob :
      |aperyF5AnalyticRatio zt - aperyZeta3Series|
        ≤ K_frob * d := by
    simpa [zt, d, mul_assoc] using hf_bound t ht_nonneg
  have htri :
      |sol.trajectory t aperyF5_iR - aperyZeta3Series|
        ≤ |sol.trajectory t aperyF5_iR - aperyF5AnalyticRatio zt| +
          |aperyF5AnalyticRatio zt - aperyZeta3Series| :=
    abs_sub_le _ _ _
  calc
    |sol.trajectory t aperyF5_iR - aperyZeta3Series|
        ≤ |sol.trajectory t aperyF5_iR - aperyF5AnalyticRatio zt| +
            |aperyF5AnalyticRatio zt - aperyZeta3Series| := htri
    _ ≤ K_track * d + K_frob * d := add_le_add htrack hfrob
    _ = (K_track + K_frob) * d := by ring
    _ = (K_track + K_frob) *
          |aperyConifoldZ1 - sol.trajectory t aperyF5_iZ| *
          Real.sqrt |aperyConifoldZ1 - sol.trajectory t aperyF5_iZ| := by
        simp [d, zt, aperyF5_iZ, mul_assoc]

/-- The `z`-coordinate of a PIVP solution is continuous on every nonnegative
compact time interval. -/
lemma aperyF5_z_coordinate_continuousOn_Icc
    (init : Fin 8 → ℚ)
    (sol : PIVP.Solution (apery8VarPolyPIVP init).toPIVP)
    (T : ℝ) :
    ContinuousOn (fun t : ℝ => sol.trajectory t aperyF5_iZ)
      (Set.Icc (0 : ℝ) T) := by
  intro t ht
  have h_ode : HasDerivAt sol.trajectory
      ((apery8VarPolyPIVP init).toPIVP.field (sol.trajectory t)) t :=
    sol.is_solution t ht.1
  have h_z : HasDerivAt (fun u : ℝ => sol.trajectory u aperyF5_iZ)
      ((apery8VarPolyPIVP init).toPIVP.field (sol.trajectory t) aperyF5_iZ) t :=
    hasDerivAt_pi.mp h_ode aperyF5_iZ
  exact h_z.continuousAt.continuousWithinAt

/-- A positive exponential envelope eventually lies below any positive
threshold. -/
lemma aperyF5_exp_decay_eventually_below
    {C lam δ : ℝ} (hC : 0 < C) (hlam : 0 < lam) (hδ : 0 < δ) :
    ∃ T₀ : ℝ, 0 ≤ T₀ ∧
      ∀ t : ℝ, T₀ ≤ t → C * Real.exp (-(lam * t)) ≤ δ := by
  refine ⟨max 0 (Real.log (C / δ) / lam), le_max_left _ _, ?_⟩
  intro t ht
  have hT_log : Real.log (C / δ) / lam ≤ t :=
    le_trans (le_max_right _ _) ht
  have hlog_le : Real.log (C / δ) ≤ lam * t := by
    calc
      Real.log (C / δ) = (Real.log (C / δ) / lam) * lam := by
        field_simp [ne_of_gt hlam]
      _ ≤ t * lam := mul_le_mul_of_nonneg_right hT_log (le_of_lt hlam)
      _ = lam * t := by ring
  have hratio_pos : 0 < C / δ := div_pos hC hδ
  have hratio_le_exp : C / δ ≤ Real.exp (lam * t) :=
    (Real.log_le_iff_le_exp hratio_pos).mp hlog_le
  have hexp_pos : 0 < Real.exp (lam * t) := Real.exp_pos _
  have hmain : (C / δ) / Real.exp (lam * t) ≤ 1 := by
    rw [div_le_one hexp_pos]
    exact hratio_le_exp
  have hrewrite :
      C * Real.exp (-(lam * t)) =
        δ * ((C / δ) / Real.exp (lam * t)) := by
    rw [Real.exp_neg]
    field_simp [ne_of_gt hδ, ne_of_gt hexp_pos]
  rw [hrewrite]
  exact (mul_le_mul_of_nonneg_left hmain (le_of_lt hδ)).trans_eq (mul_one δ)

/-- Compactness of the pre-entry trajectory segment gives a strict subinterval
of `(0, z₁)` containing the `z`-image. -/
lemma aperyF5Trajectory_prewindow_Icc_bounds
    (init : Fin 8 → ℚ)
    (sol : PIVP.Solution (apery8VarPolyPIVP init).toPIVP)
    (T₀ : ℝ) (hT₀ : 0 ≤ T₀)
    (hz_in_disk :
      ∀ τ : ℝ, 0 ≤ τ →
        0 < sol.trajectory τ aperyF5_iZ ∧
          sol.trajectory τ aperyF5_iZ < aperyConifoldZ1) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ b < aperyConifoldZ1 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T₀,
        a ≤ sol.trajectory t aperyF5_iZ ∧
          sol.trajectory t aperyF5_iZ ≤ b := by
  let zfun : ℝ → ℝ := fun t => sol.trajectory t aperyF5_iZ
  have h_compact : IsCompact (Set.Icc (0 : ℝ) T₀) := isCompact_Icc
  have h_nonempty : (Set.Icc (0 : ℝ) T₀).Nonempty :=
    ⟨0, ⟨le_refl _, hT₀⟩⟩
  have hz_cont : ContinuousOn zfun (Set.Icc (0 : ℝ) T₀) :=
    aperyF5_z_coordinate_continuousOn_Icc init sol T₀
  obtain ⟨t_max, ht_max_mem, h_max⟩ :=
    h_compact.exists_isMaxOn h_nonempty hz_cont
  obtain ⟨t_min, ht_min_mem, h_min⟩ :=
    h_compact.exists_isMinOn h_nonempty hz_cont
  refine ⟨zfun t_min, zfun t_max, ?_, ?_, ?_, ?_⟩
  · exact (hz_in_disk t_min ht_min_mem.1).1
  · exact h_max ht_min_mem
  · exact (hz_in_disk t_max ht_max_mem.1).2
  · intro t ht
    exact ⟨h_min ht, h_max ht⟩

/-- Trajectory-specific local-to-global Frobenius ratio bound.

This is the remaining compact/F6 assembly after isolating the pure analytic
facts:

* use F6 to enter the local Frobenius `δ`-window;
* use `aperyF5AnalyticRatio_error_bdd_on_Icc` on the compact pre-window
  `z`-image;
* use positivity of the distance from the compact pre-window image to the
  conifold to convert the transient bound into the `3/2` scale;
* combine the transient and eventual constants.
-/
theorem aperyF5Trajectory_local_F6_compact_along_bound
    (init : Fin 8 → ℚ)
    (sol : PIVP.Solution (apery8VarPolyPIVP init).toPIVP)
    (hbdd : (apery8VarPolyPIVP init).toPIVP.IsBounded sol.trajectory)
    (hz_init : (0 : ℝ) < ((init aperyF5_iZ : ℚ) : ℝ) ∧
                 ((init aperyF5_iZ : ℚ) : ℝ) < aperyConifoldZ1)
    (hf : AperyFrobeniusRatioBound)
    (hz_in_disk :
      ∀ τ : ℝ, 0 ≤ τ →
        0 < sol.trajectory τ aperyF5_iZ ∧
          sol.trajectory τ aperyF5_iZ < aperyConifoldZ1) :
    AperyFrobeniusRatioBoundAlong init sol := by
  rcases hf with ⟨K_frob, hK_frob, δ, hδ, hf_bound⟩
  obtain ⟨C, lam, hC, hlam, hz_exp⟩ :=
    apery_z_component_exponential_to_conifold init sol hbdd
      (by simpa [aperyF5_iZ] using hz_init)
  obtain ⟨T₀, hT₀_nonneg, htail_exp⟩ :=
    aperyF5_exp_decay_eventually_below hC hlam (half_pos hδ)
  obtain ⟨a, b, ha, hab, hb, hbounds⟩ :=
    aperyF5Trajectory_prewindow_Icc_bounds init sol T₀ hT₀_nonneg hz_in_disk
  obtain ⟨M, hM, hM_bound⟩ :=
    aperyF5AnalyticRatio_error_bdd_on_Icc a b ha hab hb
  let dmin : ℝ := (aperyConifoldZ1 - b) * Real.sqrt (aperyConifoldZ1 - b)
  have hbase_pos : 0 < aperyConifoldZ1 - b := sub_pos.mpr hb
  have hdmin_pos : 0 < dmin := by
    exact mul_pos hbase_pos (Real.sqrt_pos.mpr hbase_pos)
  let K_trans : ℝ := M / dmin
  let K : ℝ := max K_frob K_trans
  refine ⟨K, ?_, ?_⟩
  · exact lt_of_lt_of_le hK_frob (le_max_left _ _)
  intro t ht_nonneg
  let zt : ℝ := sol.trajectory t aperyF5_iZ
  let d : ℝ := |aperyConifoldZ1 - zt| * Real.sqrt |aperyConifoldZ1 - zt|
  have hz := hz_in_disk t ht_nonneg
  have hd_nonneg : 0 ≤ d := by
    exact mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  by_cases htail : T₀ ≤ t
  · have h_abs_eq : |aperyConifoldZ1 - zt| = aperyConifoldZ1 - zt := by
      exact abs_of_nonneg (sub_nonneg.mpr (le_of_lt hz.2))
    have hnear : aperyConifoldZ1 - zt < δ := by
      rw [← h_abs_eq]
      have hhalf_lt : δ / 2 < δ := by linarith
      exact lt_of_le_of_lt (le_trans (hz_exp t ht_nonneg) (htail_exp t htail)) hhalf_lt
    have hlocal :
        |aperyF5AnalyticRatio zt - aperyZeta3Series| ≤ K_frob * d := by
      simpa [zt, d, mul_assoc] using hf_bound zt hz.1 hz.2 hnear
    calc
      |aperyF5AnalyticRatio (sol.trajectory t aperyF5_iZ) - aperyZeta3Series|
          ≤ K_frob * d := by simpa [zt] using hlocal
      _ ≤ K * d := mul_le_mul_of_nonneg_right (le_max_left _ _) hd_nonneg
      _ = K * |aperyConifoldZ1 - sol.trajectory t aperyF5_iZ| *
            Real.sqrt |aperyConifoldZ1 - sol.trajectory t aperyF5_iZ| := by
          simp [K, d, zt, mul_assoc]
  · have ht_le_T₀ : t ≤ T₀ := le_of_not_ge htail
    have ht_mem : t ∈ Set.Icc (0 : ℝ) T₀ := ⟨ht_nonneg, ht_le_T₀⟩
    have hzt_bounds := hbounds t ht_mem
    have hcompact :
        |aperyF5AnalyticRatio zt - aperyZeta3Series| ≤ M := by
      exact hM_bound zt ⟨hzt_bounds.1, hzt_bounds.2⟩
    have h_abs_eq : |aperyConifoldZ1 - zt| = aperyConifoldZ1 - zt := by
      exact abs_of_nonneg (sub_nonneg.mpr (le_of_lt hz.2))
    have hbase_le : aperyConifoldZ1 - b ≤ aperyConifoldZ1 - zt := by
      linarith [hzt_bounds.2]
    have hsqrt_le :
        Real.sqrt (aperyConifoldZ1 - b) ≤ Real.sqrt (aperyConifoldZ1 - zt) :=
      Real.sqrt_le_sqrt hbase_le
    have hdmin_le : dmin ≤ d := by
      change (aperyConifoldZ1 - b) * Real.sqrt (aperyConifoldZ1 - b) ≤
        |aperyConifoldZ1 - zt| * Real.sqrt |aperyConifoldZ1 - zt|
      rw [h_abs_eq]
      exact mul_le_mul hbase_le hsqrt_le (Real.sqrt_nonneg _)
        (sub_nonneg.mpr (le_of_lt hz.2))
    have hM_le_trans : M ≤ K_trans * d := by
      have hKtrans_nonneg : 0 ≤ K_trans := by
        exact div_nonneg (le_of_lt hM) (le_of_lt hdmin_pos)
      calc
        M = K_trans * dmin := by
          simp [K_trans]
          field_simp [ne_of_gt hdmin_pos]
        _ ≤ K_trans * d := mul_le_mul_of_nonneg_left hdmin_le hKtrans_nonneg
    have hKtrans_le : K_trans ≤ K := le_max_right _ _
    calc
      |aperyF5AnalyticRatio (sol.trajectory t aperyF5_iZ) - aperyZeta3Series|
          ≤ M := by simpa [zt] using hcompact
      _ ≤ K_trans * d := hM_le_trans
      _ ≤ K * d := mul_le_mul_of_nonneg_right hKtrans_le hd_nonneg
      _ = K * |aperyConifoldZ1 - sol.trajectory t aperyF5_iZ| *
            Real.sqrt |aperyConifoldZ1 - sol.trajectory t aperyF5_iZ| := by
          simp [K, d, zt, mul_assoc]

/-- Local Frobenius control globalized along a bounded PIVP trajectory.

Proof plan:

* F6 (`apery_z_component_exponential_to_conifold`) puts `z(t)` into the
  local `δ`-window after some time `T₀`;
* on `[T₀, ∞)` the local Frobenius estimate applies directly;
* on `[0, T₀]`, boundedness of the trajectory and compactness of the
  `z`-image give a finite transient bound for the analytic ratio, while
  the distance to the conifold has a positive lower bound;
* combine the two constants.

The missing analytic ingredient is the compact transient bound for
`aperyF5AnalyticRatio`, requiring continuity of the differentiated Apéry
series ratio and non-vanishing of `A''` on compact subintervals of
`(0, z₁)`. -/
theorem aperyFrobeniusRatioBound_along_of_local_F6_compact
    (init : Fin 8 → ℚ)
    (sol : PIVP.Solution (apery8VarPolyPIVP init).toPIVP)
    (hbdd : (apery8VarPolyPIVP init).toPIVP.IsBounded sol.trajectory)
    (hz_init : (0 : ℝ) < ((init aperyF5_iZ : ℚ) : ℝ) ∧
                 ((init aperyF5_iZ : ℚ) : ℝ) < aperyConifoldZ1)
    (hf : AperyFrobeniusRatioBound)
    (hz_in_disk :
      ∀ τ : ℝ, 0 ≤ τ →
        0 < sol.trajectory τ aperyF5_iZ ∧
          sol.trajectory τ aperyF5_iZ < aperyConifoldZ1) :
    AperyFrobeniusRatioBoundAlong init sol := by
  exact aperyF5Trajectory_local_F6_compact_along_bound
    init sol hbdd hz_init hf hz_in_disk

/-- The intended local split theorem.

The remaining structural gap is not the triangle inequality; it is the
globalization step from the local Frobenius window in
`AperyFrobeniusRatioBound` to all times `t ≥ 0`.  Filling this requires:

1. scalar F6 entry of `z(t)` into the `δ`-window and monotone stay there;
2. a compact/preasymptotic bound for the finite initial segment; and
3. if tracking is first proved in exponential form, comparison of that
   exponential term with `|z₁ - z(t)|^(3/2)`.
-/
theorem aperyConifoldThreeHalvesBound_of_split
    (init : Fin 8 → ℚ)
    (sol : PIVP.Solution (apery8VarPolyPIVP init).toPIVP)
    (hbdd : (apery8VarPolyPIVP init).toPIVP.IsBounded sol.trajectory)
    (hz_init : (0 : ℝ) < ((init aperyF5_iZ : ℚ) : ℝ) ∧
                 ((init aperyF5_iZ : ℚ) : ℝ) < aperyConifoldZ1)
    (hf : AperyFrobeniusRatioBound)
    (ht : AperyPIVPRatioTracking init sol)
    (hz_in_disk :
      ∀ τ : ℝ, 0 ≤ τ →
        0 < sol.trajectory τ aperyF5_iZ ∧
          sol.trajectory τ aperyF5_iZ < aperyConifoldZ1) :
    AperyConifoldThreeHalvesBound init sol := by
  exact aperyConifoldThreeHalvesBound_of_along_split init sol
    (aperyFrobeniusRatioBound_along_of_local_F6_compact
      init sol hbdd hz_init hf hz_in_disk)
    ht

end Ripple.Number
