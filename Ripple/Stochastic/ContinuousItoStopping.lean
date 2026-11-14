import Ripple.Stochastic.ContinuousItoStoppingGrid
import Ripple.Stochastic.DyadicStoppingApproximation
import Ripple.Stochastic.FilteredItoIntegralProcessIsometry

/-!
# Random stopping of the installed continuous Itô integral

Finite-grid stopping is passed to a bounded stopping time by upper dyadic
approximation. The original continuous path converges at the stopped arguments;
the stopped integrands converge in predictable L² and their integrals converge
in the uniform path L² norm. One subsequence supplies a simultaneous identity
on the whole compact interval.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Ripple.Stochastic.ContinuousItoStopping
open FilteredItoIntegralL2 FilteredItoIntegralCLM FilteredItoIntegralProcessGeneral
open AdaptedContinuousSpace ContinuousItoElementary ContinuousItoConsistency
open ContinuousItoStoppingGrid StoppedPredictableIntegrand StoppedIntegrandLimit

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
  [IsFilteredPreBrownian B F μ]

/-- The final limit passage is at entire paths. Its finite-grid hypotheses
are instantiated by the dyadic construction below. -/
theorem continuousIto_stopped_of_grid_approx (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    {τ : Ω → ℝ≥0} {τn : ℕ → Ω → ℝ≥0}
    (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτn : ∀ n, IsStoppingTime F (fun ω => (τn n ω : WithTop ℝ≥0)))
    (hle : ∀ n ω, τ ω ≤ τn n ω)
    (hlim : ∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω)))
    (q : ℕ → ℕ → ℝ≥0) (hq : ∀ n, StrictMono (q n)) (hz : ∀ n, q n 0 = 0)
    (N : ℕ → ℕ) (hgrid : ∀ n ω, ∃ k ≤ N n, τn n ω = q n k)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    ∀ᵐ ω ∂μ, ∀ t : Set.Icc (0 : ℝ≥0) T,
      representative (continuousIto T hB hBmeas (stoppedIntegrand T hBmeas hτ φ)) ω t =
      representative (continuousIto T hB hBmeas φ) ω (stoppedWindowTime T τ ω t) := by
  obtain ⟨ns, hns, hpath⟩ :=
    exists_stopped_uniform_path_subsequence T hBmeas hτ hτn hle hlim φ hB
  have hall : ∀ᵐ ω ∂μ, ∀ n, ∀ t : Set.Icc (0 : ℝ≥0) T,
      representative (continuousIto T hB hBmeas (stoppedIntegrand T hBmeas (hτn n) φ)) ω t =
      representative (continuousIto T hB hBmeas φ) ω (stoppedWindowTime T (τn n) ω t) :=
    ae_all_iff.mpr fun n =>
      continuousIto_stopped_grid T hB hBmeas (q n) (hq n) (hz n) (N n) (τn n)
        (hτn n) (hgrid n) φ
  filter_upwards [hpath, hall] with ω hpathω heq t
  have htime : Tendsto (fun n => stoppedWindowTime T (τn (ns n)) ω t) atTop
      (𝓝 (stoppedWindowTime T τ ω t)) := by
    apply tendsto_subtype_rng.mpr
    exact tendsto_const_nhds.min ((hlim ω).comp hns.tendsto_atTop)
  have hleft := ((ContinuousMap.evalCLM ℝ t).continuous.continuousAt.tendsto).comp hpathω
  have hright := (representative (continuousIto T hB hBmeas φ) ω).continuous.continuousAt.tendsto.comp htime
  exact tendsto_nhds_unique hleft
    (hright.congr' (Eventually.of_forall fun n => (heq (ns n) t).symm))

/-- Random stopping identity for a bounded finite stopping time, with all
approximation and density premises discharged by the concrete constructions. -/
theorem continuousIto_stopped_bounded (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (hbound : ∀ ω, τ ω ≤ T)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    ∀ᵐ ω ∂μ, ∀ t : Set.Icc (0 : ℝ≥0) T,
      representative (continuousIto T hB hBmeas (stoppedIntegrand T hBmeas hτ φ)) ω t =
      representative (continuousIto T hB hBmeas φ) ω (stoppedWindowTime T τ ω t) := by
  exact continuousIto_stopped_of_grid_approx T hB hBmeas hτ
    (DyadicStoppingApproximation.dyadicStop_isStoppingTime τ hτ)
    (fun n ω => DyadicStoppingApproximation.le_dyadicStop n τ ω)
    (DyadicStoppingApproximation.dyadicStop_tendsto τ)
    DyadicStoppingApproximation.dyadicGrid
    DyadicStoppingApproximation.dyadicGrid_strictMono
    DyadicStoppingApproximation.dyadicGrid_zero
    (fun n => ⌈T * DyadicStoppingApproximation.dyadicScale n⌉₊)
    (fun n ω => DyadicStoppingApproximation.dyadicStop_mem_grid n hbound ω) φ

/-- A finite cap of an extended stopping time. The finite minimum is taken
before removing the top constructor. An infinite stop therefore leaves the
process running up to the cap. -/
def cappedStopTime (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (min (τ ω) (T : WithTop ℝ≥0)).untop
    (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _))

@[simp] theorem coe_cappedStopTime (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    (cappedStopTime T τ ω : WithTop ℝ≥0) = min (τ ω) (T : WithTop ℝ≥0) := by
  simp [cappedStopTime]

theorem cappedStopTime_le (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    cappedStopTime T τ ω ≤ T := by
  apply WithTop.coe_le_coe.mp
  rw [coe_cappedStopTime]
  exact min_le_right _ _

theorem cappedStopTime_isStoppingTime (T : ℝ≥0) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) :
    IsStoppingTime F (fun ω => (cappedStopTime T τ ω : WithTop ℝ≥0)) := by
  simpa only [coe_cappedStopTime] using hτ.min_const T

/-- Capping beyond the integration horizon preserves the stopped L² element. -/
theorem stoppedIntegrand_capped (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    stoppedIntegrand T hBmeas (cappedStopTime_isStoppingTime T hτ) φ =
      stoppedIntegrand T hBmeas hτ φ := by
  apply Lp.ext
  filter_upwards [stoppedIntegrand_coeFn T hBmeas (cappedStopTime_isStoppingTime T hτ) φ,
    stoppedIntegrand_coeFn T hBmeas hτ φ,
    BoundedPredictableApproximation.ae_window (μ := μ) (F := F) T hBmeas] with z hc hτz hz
  rw [hc, hτz]
  have hmem : z ∈ stoppingRegion (fun ω => (cappedStopTime T τ ω : WithTop ℝ≥0)) ↔
      z ∈ stoppingRegion τ := by
    simp only [stoppingRegion, Set.mem_setOf_eq, coe_cappedStopTime, le_min_iff,
      WithTop.coe_le_coe, hz.2, and_true]
  by_cases h : z ∈ stoppingRegion τ
  · rw [Set.indicator_of_mem (hmem.2 h), Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem (fun h' => h (hmem.1 h')), Set.indicator_of_notMem h]

/-- Extended stopping times, including infinite inverse clocks, satisfy the
same simultaneous identity for every installed predictable L² integrand. -/
theorem continuousIto_stopped (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    ∀ᵐ ω ∂μ, ∀ t : Set.Icc (0 : ℝ≥0) T,
      representative (continuousIto T hB hBmeas (stoppedIntegrand T hBmeas hτ φ)) ω t =
      representative (continuousIto T hB hBmeas φ) ω
        (stoppedWindowTime T (cappedStopTime T τ) ω t) := by
  have h := continuousIto_stopped_bounded T hB hBmeas
    (cappedStopTime_isStoppingTime T hτ) (cappedStopTime_le T τ) φ
  rwa [stoppedIntegrand_capped T hBmeas hτ φ] at h

end Ripple.Stochastic.ContinuousItoStopping
