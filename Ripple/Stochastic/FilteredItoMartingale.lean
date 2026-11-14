/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/

import Ripple.Stochastic.FilteredItoIntegralProcessIsometry

/-!
# A strongly adapted representative of the predictable L² Itô integral

Conditional expectations of the terminal integral select strongly measurable
representatives. The resulting process is a martingale for the prescribed
filtration and agrees at every fixed time almost everywhere with the L² integral.
This construction asserts no sample-path continuity.
-/


namespace Ripple.Stochastic.FilteredItoIntegralProcessGeneral

open MeasureTheory ProbabilityTheory
open FilteredItoIntegralL2 FilteredItoIntegralCLM
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {𝓖 : Filtration ℝ≥0 mΩ}
  [IsFilteredPreBrownian B 𝓖 μ]

/-- A strongly adapted representative selected by conditional expectation of the
terminal integral. It represents the integral stopped at the deterministic horizon. -/
noncomputable def itoIntegralProcess (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas)) : ℝ≥0 → Ω → ℝ :=
  fun t => μ[(itoIntegralCLM_T (𝓖 := 𝓖) T hBmeas φ : Ω → ℝ) | 𝓖 t]

/-- The selected Itô integral process is a martingale for the prescribed filtration. -/
theorem itoIntegralProcess_isMartingale (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas)) :
    Martingale (itoIntegralProcess (𝓖 := 𝓖) T hBmeas φ) 𝓖 μ := by
  exact martingale_condExp (itoIntegralCLM_T (𝓖 := 𝓖) T hBmeas φ : Ω → ℝ) 𝓖 μ

/-- At every deterministic time the selected process agrees a.e. with the L²
extension of elementary stochastic integration. -/
theorem itoIntegralProcess_ae_eq_itoProcessCLM (T t : ℝ≥0)
    (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas)) :
    itoIntegralProcess (𝓖 := 𝓖) T hBmeas φ t =ᵐ[μ]
      (itoProcessCLM (𝓖 := 𝓖) T t hBmeas φ : Ω → ℝ) := by
  rw [itoProcessCLM_eq_condExp (𝓖 := 𝓖)]
  have h := (Lp.memLp (itoIntegralCLM_T (𝓖 := 𝓖) T hBmeas φ)).condExpL2_ae_eq_condExp
    (𝕜 := ℝ) (𝓖.le t)
  rw [Lp.toLp_coeFn] at h
  exact h.symm

/-- The martingale representative satisfies the time-indexed Itô isometry. -/
theorem itoIntegralProcess_sq_integral {t T : ℝ≥0} (htT : t ≤ T)
    (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas)) :
    ∫ ω, (itoIntegralProcess (𝓖 := 𝓖) T hBmeas φ t ω) ^ 2 ∂μ =
      ∫ z in (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)), (φ z) ^ 2
        ∂(trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) := by
  rw [← itoProcessCLM_norm_sq (𝓖 := 𝓖) htT hBmeas φ, lp_two_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [itoIntegralProcess_ae_eq_itoProcessCLM (𝓖 := 𝓖) T t hBmeas φ]
    with ω hω
  rw [hω]

end Ripple.Stochastic.FilteredItoIntegralProcessGeneral
