import Ripple.Stochastic.ElementaryStoppingIntegral
import Ripple.Stochastic.ContinuousItoConsistency
import Ripple.Stochastic.StoppedIntegrandLimit

/-!
# Finite-grid stopping for the installed continuous Itô integral

The elementary identity is extended through the actual predictable L² domain.
Two path-valued L² limits supply a common subsequence converging uniformly in
time almost surely. Consequently random evaluation uses one exceptional set.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Ripple.Stochastic.ContinuousItoStoppingGrid
open FilteredItoIntegralL2 FilteredItoIntegralCLM FilteredItoIntegralProcess
open ContinuousItoElementary ContinuousItoConstruction AdaptedContinuousSpace
open ContinuousItoConsistency ElementaryStoppingIntegral StoppedPredictableIntegrand

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
  [IsFilteredPreBrownian B F μ]

/-- Finite-time evaluation never leaves the compact integration window. -/
def stoppedWindowTime (T : ℝ≥0) (τ : Ω → ℝ≥0) (ω : Ω)
    (t : Set.Icc (0 : ℝ≥0) T) : Set.Icc (0 : ℝ≥0) T :=
  ⟨min t.val (τ ω), zero_le, (min_le_left _ _).trans t.property.2⟩

/-- The installed continuous representative of an elementary integral agrees
with the finite-sum formula on one event for the whole time window. -/
theorem continuousIto_simple_ae (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (V : TBoundedSP (𝓖 := F) T hBmeas) :
    ∀ᵐ ω ∂μ, ∀ t : Set.Icc (0 : ℝ≥0) T,
      representative (continuousIto T hB hBmeas (simpleAssembly_T (μ := μ) T hBmeas V)) ω t =
        itoSimpleProcess hBmeas V.val t.val ω := by
  have he : continuousIto T hB hBmeas (simpleAssembly_T (μ := μ) T hBmeas V) =
      boundedSimplePathLp T hB hBmeas V :=
    continuousIntegral_simple _ (simpleAssembly_T_denseRange T hBmeas) _ _
      (boundedSimplePathLp_norm_le T hB hBmeas) V
  rw [he]
  filter_upwards [representative_ae (boundedSimplePathLp (μ := μ) T hB hBmeas V),
    (simpleIntegralPath_memLp (μ := μ) T hB hBmeas V.val).coeFn_toLp] with ω hr hs t
  have heq : representative (boundedSimplePathLp (μ := μ) T hB hBmeas V) ω =
      simpleIntegralPath T hB V.val ω := hr.symm.trans hs
  rw [heq, simpleIntegralPath_apply T hB hBmeas V.val ω t]

/-- Multiply an installed simple process by the finite-grid stopping mask,
then explicitly truncate its finite support to the integration horizon. -/
def stoppedSimple (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (q : ℕ → ℝ≥0) (hq : StrictMono q) (N : ℕ) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (V : TBoundedSP (𝓖 := F) T hBmeas) : TBoundedSP (𝓖 := F) T hBmeas :=
  truncateSimple T hBmeas (SimpleProcess.map₂ (ContinuousLinearMap.mul ℝ ℝ)
    (survivalGrid q hq.monotone N τ (fun i => measurableSet_survival hτ (q i))) V.val)

/-- The simple-process construction is the same L² element as indicator
multiplication in the installed predictable domain. -/
theorem stoppedSimple_assembly (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (q : ℕ → ℝ≥0) (hq : StrictMono q) (hz : q 0 = 0) (N : ℕ) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (hgrid : ∀ ω, ∃ k ≤ N, τ ω = q k) (V : TBoundedSP (𝓖 := F) T hBmeas) :
    simpleAssembly_T (μ := μ) T hBmeas (stoppedSimple T hBmeas q hq N τ hτ V) =
      stoppedIntegrand T hBmeas hτ (simpleAssembly_T (μ := μ) T hBmeas V) := by
  apply Lp.ext
  filter_upwards [(memLp_uncurry_trim_T T hBmeas
      (stoppedSimple T hBmeas q hq N τ hτ V).val).coeFn_toLp,
    stoppedIntegrand_coeFn T hBmeas hτ (simpleAssembly_T (μ := μ) T hBmeas V),
    (memLp_uncurry_trim_T (μ := μ) T hBmeas V.val).coeFn_toLp,
    BoundedPredictableApproximation.ae_window (μ := μ) (F := F) T hBmeas]
      with z hleft hright hV hzwin
  refine hleft.trans ?_
  rw [hright]
  change (stoppedSimple T hBmeas q hq N τ hτ V).val z.1 z.2 = _
  rw [stoppedSimple, truncateSimple_apply T hBmeas _ hzwin.1 hzwin.2,
    SimpleProcess.coe_map₂]
  beta_reduce
  rw [ContinuousLinearMap.mul_apply', survivalGrid_apply q hq hz N τ _ hgrid]
  by_cases h : 0 < z.1 ∧ z.1 ≤ τ z.2
  · simp only [if_pos h, one_mul, Set.indicator_of_mem
      (show z ∈ stoppingRegion (fun ω => (τ ω : WithTop ℝ≥0)) from
        ⟨h.1, WithTop.coe_le_coe.2 h.2⟩)]
    exact hV.symm
  · simp only [if_neg h, zero_mul, Set.indicator_of_notMem
      (show z ∉ stoppingRegion (fun ω => (τ ω : WithTop ℝ≥0)) from
        fun hm => h ⟨hm.1, WithTop.coe_le_coe.1 hm.2⟩)]

/-- The continuous elementary realizations satisfy the stopping identity
simultaneously at every time in the compact window. -/
theorem continuousIto_stopped_simple_grid (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (q : ℕ → ℝ≥0) (hq : StrictMono q) (hz : q 0 = 0) (N : ℕ) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (hgrid : ∀ ω, ∃ k ≤ N, τ ω = q k) (V : TBoundedSP (𝓖 := F) T hBmeas) :
    ∀ᵐ ω ∂μ, ∀ t : Set.Icc (0 : ℝ≥0) T,
      representative (continuousIto T hB hBmeas
        (stoppedIntegrand T hBmeas hτ (simpleAssembly_T (μ := μ) T hBmeas V))) ω t =
      representative (continuousIto T hB hBmeas (simpleAssembly_T (μ := μ) T hBmeas V)) ω
        (stoppedWindowTime T τ ω t) := by
  rw [← stoppedSimple_assembly T hBmeas q hq hz N τ hτ hgrid V]
  filter_upwards [continuousIto_simple_ae T hB hBmeas
    (stoppedSimple T hBmeas q hq N τ hτ V),
    continuousIto_simple_ae T hB hBmeas V] with ω hleft hright t
  rw [hleft, hright]
  change itoSimpleProcess hBmeas (truncateSimple T hBmeas _).val t.val ω = _
  rw [itoSimpleProcess_truncate T hBmeas _ t.property.2]
  exact itoSimpleProcess_stopped_grid B hBmeas V.val q hq hz N τ hτ hgrid t.val ω

/-- Norm convergence of actual path L² elements yields an a.e. uniformly
convergent subsequence for their selected continuous representatives. -/
theorem exists_representative_subsequence {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {X : ℕ → PathLp K μ} {Y : PathLp K μ}
    (hX : Tendsto X atTop (𝓝 Y)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂μ,
      Tendsto (fun n => representative (X (ns n)) ω) atTop (𝓝 (representative Y ω)) := by
  have hm : TendstoInMeasure μ (fun n => representative (X n)) atTop (representative Y) :=
    TendstoInMeasure.congr (fun n => representative_ae (X n)) (representative_ae Y)
      (tendstoInMeasure_of_tendsto_Lp hX)
  exact hm.exists_seq_tendsto_ae

/-- Finite-grid random stopping for every installed predictable L² integrand.
The two a.e. path limits justify evaluation at the sample-dependent stopped time. -/
theorem continuousIto_stopped_grid (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (q : ℕ → ℝ≥0) (hq : StrictMono q) (hz : q 0 = 0) (N : ℕ) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (hgrid : ∀ ω, ∃ k ≤ N, τ ω = q k)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    ∀ᵐ ω ∂μ, ∀ t : Set.Icc (0 : ℝ≥0) T,
      representative (continuousIto T hB hBmeas (stoppedIntegrand T hBmeas hτ φ)) ω t =
      representative (continuousIto T hB hBmeas φ) ω (stoppedWindowTime T τ ω t) := by
  obtain ⟨g, hg, hlim⟩ := mem_closure_iff_seq_limit.mp
    ((simpleAssembly_T_denseRange (𝓖 := F) (μ := μ) T hBmeas).closure_range.ge
      (Set.mem_univ φ))
  choose V hV using hg
  have hpath := (continuousIto T hB hBmeas).continuous.continuousAt.tendsto.comp hlim
  obtain ⟨u, hu, hPu⟩ := exists_representative_subsequence hpath
  have hstopped : Tendsto
      (fun n => continuousIto T hB hBmeas (stoppedIntegrand T hBmeas hτ (g (u n)))) atTop
      (𝓝 (continuousIto T hB hBmeas (stoppedIntegrand T hBmeas hτ φ))) := by
    exact (continuousIto T hB hBmeas).continuous.continuousAt.tendsto.comp
      ((StoppedIntegrandLimit.continuous_stoppedIntegrand T hBmeas hτ).continuousAt.tendsto.comp
        (hlim.comp hu.tendsto_atTop))
  obtain ⟨v, hv, hPv⟩ := exists_representative_subsequence hstopped
  have hall : ∀ᵐ ω ∂μ, ∀ n, ∀ t : Set.Icc (0 : ℝ≥0) T,
      representative (continuousIto T hB hBmeas
        (stoppedIntegrand T hBmeas hτ (g n))) ω t =
      representative (continuousIto T hB hBmeas (g n)) ω (stoppedWindowTime T τ ω t) := by
    apply ae_all_iff.mpr
    intro n
    rw [← hV n]
    exact continuousIto_stopped_simple_grid T hB hBmeas q hq hz N τ hτ hgrid (V n)
  filter_upwards [hPu, hPv, hall] with ω hleft hright heq t
  have hleft' := (((ContinuousMap.evalCLM ℝ (stoppedWindowTime T τ ω t)).continuous.tendsto _)).comp
    (hleft.comp hv.tendsto_atTop)
  have hright' := (((ContinuousMap.evalCLM ℝ t).continuous.tendsto _)).comp hright
  apply tendsto_nhds_unique hright'
  exact hleft'.congr' (Filter.Eventually.of_forall fun n => (heq (u (v n)) t).symm)

end Ripple.Stochastic.ContinuousItoStoppingGrid
