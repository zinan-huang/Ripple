import Ripple.Stochastic.StoppedPredictableIntegrand
import Ripple.Stochastic.ContinuousItoElementary
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Limits of stopped predictable integrands

Stopping times approximated from above give pointwise eventual equality of
survival masks. Dominated convergence with the original integrand squared then
gives convergence in the installed predictable L² space. Continuity of the
continuous-path Itô operator yields uniform-path L² convergence and one
subsequence converging almost everywhere in the uniform path norm.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal

namespace Ripple.Stochastic.StoppedIntegrandLimit
open StoppedPredictableIntegrand FilteredItoIntegralCLM FilteredItoIntegralL2
open ContinuousItoElementary AdaptedContinuousSpace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

/-- Above approximation retains the boundary point `t=τ(ω)`, so the masks
actually agree eventually at every point, without removing random graphs. -/
theorem stopped_indicator_eventually_eq
    {τ : Ω → ℝ≥0} {τn : ℕ → Ω → ℝ≥0}
    (hle : ∀ n ω, τ ω ≤ τn n ω)
    (hlim : ∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω)))
    (H : ℝ≥0 × Ω → ℝ) (z : ℝ≥0 × Ω) :
    ∀ᶠ n in atTop,
      (stoppingRegion (fun ω => (τn n ω : WithTop ℝ≥0))).indicator H z =
        (stoppingRegion (fun ω => (τ ω : WithTop ℝ≥0))).indicator H z := by
  by_cases hz : 0 < z.1
  · by_cases ht : z.1 ≤ τ z.2
    · exact Eventually.of_forall fun n => by
        have h1 : z ∈ stoppingRegion (fun ω => (τn n ω : WithTop ℝ≥0)) :=
          ⟨hz, WithTop.coe_le_coe.2 (ht.trans (hle n z.2))⟩
        have h2 : z ∈ stoppingRegion (fun ω => (τ ω : WithTop ℝ≥0)) :=
          ⟨hz, WithTop.coe_le_coe.2 ht⟩
        rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
    · have hlt : τ z.2 < z.1 := lt_of_not_ge ht
      filter_upwards [(tendsto_order.1 (hlim z.2)).2 z.1 hlt] with n hn
      have h1 : z ∉ stoppingRegion (fun ω => (τn n ω : WithTop ℝ≥0)) := fun h =>
        absurd (WithTop.coe_le_coe.1 h.2) (not_le.mpr hn)
      have h2 : z ∉ stoppingRegion (fun ω => (τ ω : WithTop ℝ≥0)) := fun h =>
        absurd (WithTop.coe_le_coe.1 h.2) ht
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
  · exact Eventually.of_forall fun n => by
      have h1 : z ∉ stoppingRegion (fun ω => (τn n ω : WithTop ℝ≥0)) := fun h => hz h.1
      have h2 : z ∉ stoppingRegion (fun ω => (τ ω : WithTop ℝ≥0)) := fun h => hz h.1
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]

section FixedStopping
variable (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)

/-- Multiplication by the survival indicator is a contraction in predictable L². -/
theorem stoppedIntegrand_sub_norm_le
    (φ ψ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    ‖stoppedIntegrand T hBmeas hτ φ - stoppedIntegrand T hBmeas hτ ψ‖ ≤ ‖φ - ψ‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub (stoppedIntegrand T hBmeas hτ φ)
      (stoppedIntegrand T hBmeas hτ ψ),
    stoppedIntegrand_coeFn T hBmeas hτ φ,
    stoppedIntegrand_coeFn T hBmeas hτ ψ, Lp.coeFn_sub φ ψ] with z hd hφ hψ he
  rw [hd, Pi.sub_apply, hφ, hψ, he, Pi.sub_apply]
  by_cases hz : z ∈ stoppingRegion τ
  · simp [hz]
  · simp [hz]

/-- Fixed random stopping is continuous in the original integrand. -/
theorem continuous_stoppedIntegrand :
    Continuous (stoppedIntegrand (μ := μ) T hBmeas hτ) := by
  have hLip : LipschitzWith 1 (stoppedIntegrand (μ := μ) T hBmeas hτ) := by
    apply LipschitzWith.of_dist_le_mul
    intro φ ψ
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using
      stoppedIntegrand_sub_norm_le T hBmeas hτ φ ψ
  exact hLip.continuous

end FixedStopping

section StoppingLimit
variable (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  {τ : Ω → ℝ≥0} {τn : ℕ → Ω → ℝ≥0}
  (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
  (hτn : ∀ n, IsStoppingTime F (fun ω => (τn n ω : WithTop ℝ≥0)))
  (hle : ∀ n ω, τ ω ≤ τn n ω)
  (hlim : ∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω)))
  (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))

include hle hlim in
/-- Above approximation of finite stopping times gives L² convergence of the
stopped integrands, for every predictable square-integrable integrand. -/
theorem stoppedIntegrand_tendsto :
    Tendsto (fun n => stoppedIntegrand T hBmeas (hτn n) φ) atTop
      (𝓝 (stoppedIntegrand T hBmeas hτ φ)) := by
  let ν := trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas
  let f := fun n => stoppedIntegrand T hBmeas (hτn n) φ
  let g := stoppedIntegrand T hBmeas hτ φ
  let d : ℕ → ℝ≥0 × Ω → ℝ := fun n z =>
    (stoppingRegion (fun ω => (τn n ω : WithTop ℝ≥0))).indicator φ z -
      (stoppingRegion (fun ω => (τ ω : WithTop ℝ≥0))).indicator φ z
  have hdmem : ∀ n, MemLp (d n) 2 ν := fun n =>
    (memLp_stopped (hτn n) (Lp.memLp φ)).sub (memLp_stopped hτ (Lp.memLp φ))
  have hraw : ∀ n, (fun z => (f n - g) z) =ᵐ[ν] d n := by
    intro n
    filter_upwards [Lp.coeFn_sub (f n) g,
      stoppedIntegrand_coeFn T hBmeas (hτn n) φ,
      stoppedIntegrand_coeFn T hBmeas hτ φ] with z hz ha hb
    exact hz.trans (congrArg₂ (fun a b : ℝ => a - b) ha hb)
  have hnormsq : ∀ n, ‖f n - g‖ ^ 2 = ∫ z, (d n z) ^ 2 ∂ν := by
    intro n
    rw [lp_two_norm_sq]
    exact integral_congr_ae ((hraw n).mono fun z hz => congrArg (fun a : ℝ => a ^ 2) hz)
  have hdconv : ∀ z, Tendsto (fun n => (d n z) ^ 2) atTop (𝓝 0) := by
    intro z
    have he : ∀ᶠ n in atTop, (d n z) ^ 2 = (0 : ℝ) := by
      filter_upwards [stopped_indicator_eventually_eq hle hlim (φ : ℝ≥0 × Ω → ℝ) z]
        with n hn
      have hd0 : d n z = 0 := by
        simp only [d]
        rw [hn, sub_self]
      rw [hd0]
      norm_num
    exact tendsto_const_nhds.congr' (he.mono fun n h => h.symm)
  have hint : Tendsto (fun n => ∫ z, (d n z) ^ 2 ∂ν) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun z => (φ z) ^ 2)
      (fun n => (hdmem n).aestronglyMeasurable.pow 2)
      (Lp.memLp φ).integrable_sq
      (fun n => ae_of_all ν fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        classical
        simp only [d, Set.indicator_apply, Pi.pow_apply]
        beta_reduce
        split_ifs <;> nlinarith [sq_nonneg (φ z)])
      (ae_of_all ν hdconv)
    simpa only [integral_zero] using h
  have hsq : Tendsto (fun n => ‖f n - g‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hnormsq] using hint
  have hnorm := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hz : Tendsto (fun n => ‖f n - g‖) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n => ‖f n - g‖) atTop (𝓝 (Real.sqrt 0)) :=
      hnorm.congr (fun n => by simp [Real.sqrt_sq_eq_abs])
    simpa using h2
  exact (tendsto_iff_dist_tendsto_zero).2 (by simpa only [dist_eq_norm] using hz)

variable [IsFilteredPreBrownian B F μ]
  (hB : ∀ ω, Continuous (fun t => B t ω))

include hle hlim in
/-- The installed continuous Itô operator carries the stopped-integrand limit
to convergence in L² of the uniform norm on continuous paths. -/
theorem continuousIto_stopped_tendsto :
    Tendsto (fun n => continuousIto T hB hBmeas
      (stoppedIntegrand T hBmeas (hτn n) φ)) atTop
      (𝓝 (continuousIto T hB hBmeas (stoppedIntegrand T hBmeas hτ φ))) :=
  (continuousIto T hB hBmeas).continuous.continuousAt.tendsto.comp
    (stoppedIntegrand_tendsto T hBmeas hτ hτn hle hlim φ)

include hle hlim in
/-- A single subsequence converges almost everywhere as entire continuous
paths, hence uniformly on the whole compact time window. -/
theorem exists_stopped_uniform_path_subsequence :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂μ,
      Tendsto (fun n => representative (continuousIto T hB hBmeas
        (stoppedIntegrand T hBmeas (hτn (ns n)) φ)) ω) atTop
        (𝓝 (representative (continuousIto T hB hBmeas
          (stoppedIntegrand T hBmeas hτ φ)) ω)) := by
  have hpath : TendstoInMeasure μ
      (fun n => representative (continuousIto T hB hBmeas
        (stoppedIntegrand T hBmeas (hτn n) φ))) atTop
      (representative (continuousIto T hB hBmeas (stoppedIntegrand T hBmeas hτ φ))) := by
    exact TendstoInMeasure.congr
      (fun n => representative_ae (continuousIto T hB hBmeas
        (stoppedIntegrand T hBmeas (hτn n) φ)))
      (representative_ae (continuousIto T hB hBmeas (stoppedIntegrand T hBmeas hτ φ)))
      (tendstoInMeasure_of_tendsto_Lp
        (continuousIto_stopped_tendsto T hBmeas hτ hτn hle hlim φ hB))
  exact hpath.exists_seq_tendsto_ae

end StoppingLimit
end Ripple.Stochastic.StoppedIntegrandLimit
