import Ripple.Stochastic.StrongSDETimeEstimate
import Ripple.Stochastic.StrongSDESolutionSpace

/-!
# Restriction between completed Itô domains on nested horizons

Both operators are the actual continuous Itô operators
against the same Brownian motion and filtration. Restriction is constructed
between their different predictable L² domains, and the intertwining identity
is proved on the installed simple processes before using density.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace Ripple.Stochastic.HorizonItoRestriction
open FilteredItoIntegralCLM FilteredItoIntegralL2 FilteredItoIntegralProcess
open AdaptedContinuousSpace ContinuousItoConstruction ContinuousItoElementary
open StoppedContinuousIto BoundedPredictableApproximation StrongSDETimeEstimate

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
  [IsFilteredPreBrownian B F μ]

theorem trimMeasure_mono {t T : ℝ≥0} (ht : t ≤ T)
    (hBmeas : ∀ u, Measurable (B u)) :
    trimMeasure_T (𝓖 := F) (μ := μ) t hBmeas ≤ trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas := by
  rw [← trimMeasure_restrict_timeBand ht hBmeas]
  exact Measure.restrict_le_self

def restrictInput {t T : ℝ≥0} (ht : t ≤ T) (hBmeas : ∀ u, Measurable (B u)) :
    Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) →L[ℝ]
      Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) t hBmeas) :=
  LinearMap.mkContinuous
    { toFun := fun U => ((Lp.memLp U).mono_measure (trimMeasure_mono ht hBmeas)).toLp U
      map_add' := fun U V => by
        apply Lp.ext
        filter_upwards [((Lp.memLp (U + V)).mono_measure (trimMeasure_mono ht hBmeas)).coeFn_toLp,
          Lp.coeFn_add (((Lp.memLp U).mono_measure (trimMeasure_mono ht hBmeas)).toLp U)
            (((Lp.memLp V).mono_measure (trimMeasure_mono ht hBmeas)).toLp V),
          ((Lp.memLp U).mono_measure (trimMeasure_mono ht hBmeas)).coeFn_toLp,
          ((Lp.memLp V).mono_measure (trimMeasure_mono ht hBmeas)).coeFn_toLp,
          ae_mono (trimMeasure_mono ht hBmeas) (Lp.coeFn_add U V)] with z hs ha hu hv huv
        simp only [hs, ha, hu, hv, huv, Pi.add_apply]
      map_smul' := fun c U => by
        apply Lp.ext
        filter_upwards [((Lp.memLp (c • U)).mono_measure (trimMeasure_mono ht hBmeas)).coeFn_toLp,
          Lp.coeFn_smul c (((Lp.memLp U).mono_measure (trimMeasure_mono ht hBmeas)).toLp U),
          ((Lp.memLp U).mono_measure (trimMeasure_mono ht hBmeas)).coeFn_toLp,
          ae_mono (trimMeasure_mono ht hBmeas) (Lp.coeFn_smul c U)] with z hs ha hu hcu
        simp only [RingHom.id_apply, hs, ha, hu, hcu, Pi.smul_apply] }
    1 (fun U => by
      rw [one_mul]
      change ‖((Lp.memLp U).mono_measure (trimMeasure_mono ht hBmeas)).toLp U‖ ≤ ‖U‖
      rw [Lp.norm_toLp, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.memLp U).2.ne
        (eLpNorm_mono_measure _ (trimMeasure_mono ht hBmeas)))

theorem restrictInput_ae {t T : ℝ≥0} (ht : t ≤ T)
    (hBmeas : ∀ u, Measurable (B u))
    (U : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    (restrictInput ht hBmeas U : ℝ≥0 × Ω → ℝ) =ᵐ[trimMeasure_T (𝓖 := F) (μ := μ) t hBmeas] U :=
  ((Lp.memLp U).mono_measure (trimMeasure_mono ht hBmeas)).coeFn_toLp

def restrictPath {t T : ℝ≥0} (ht : t ≤ T) :
    C(Window T, ℝ) →L[ℝ] C(Window t, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun s => x ⟨s.val, s.property.1, s.property.2.trans ht⟩,
        x.continuous.comp (continuous_subtype_val.subtype_mk _)⟩
      map_add' := fun _ _ => by ext s; rfl
      map_smul' := fun _ _ => by ext s; rfl }
    1 (fun x => by
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg x)).mpr
      intro s
      exact x.norm_coe_le_norm _)

def restrictPathLp {t T : ℝ≥0} (ht : t ≤ T) :
    PathLp (Window T) μ →L[ℝ] PathLp (Window t) μ :=
  (restrictPath ht).compLpL 2 μ

theorem restrictPathLp_ae {t T : ℝ≥0} (ht : t ≤ T) (X : PathLp (Window T) μ) :
    (restrictPathLp ht X : Ω → C(Window t, ℝ)) =ᵐ[μ] fun ω => restrictPath ht (X ω) := by
  have h := (restrictPath ht).coeFn_compLpL (p := 2) (μ := μ) X
  filter_upwards [h] with ω hω
  exact hω

/-- The clipped cells are now bundled with the smaller horizon bound. -/
def lowerCell (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : TBoundedSP (𝓖 := F) T hBmeas) (p : ℝ≥0 × ℝ≥0) :
    TBoundedSP (𝓖 := F) t hBmeas :=
  if hp : p ∈ V.val.value.support then
    if h : p.1 ≤ t then
      stepSP hBmeas (le_min (V.val.le_of_mem_support_value p hp) h)
        (min_le_right p.2 t) (V.val.measurable_value p)
        (fun ω => by simpa only [Real.norm_eq_abs] using V.val.value_le_valueBound p ω)
    else 0
  else 0

def lowerSP (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : TBoundedSP (𝓖 := F) T hBmeas) : TBoundedSP (𝓖 := F) t hBmeas :=
  ∑ p ∈ V.val.value.support, lowerCell T t hBmeas V p

theorem lowerSP_val (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : TBoundedSP (𝓖 := F) T hBmeas) :
    (lowerSP T t hBmeas V).val = (cutSP T t hBmeas V).val := by
  classical
  simp only [lowerSP, cutSP, Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : p.1 ≤ t
  · simp only [lowerCell, cutCell, dif_pos hp, dif_pos h]
    rfl
  · simp only [lowerCell, cutCell, dif_pos hp, dif_neg h, Submodule.coe_zero]

theorem restrictInput_simple {t T : ℝ≥0} (ht : t ≤ T)
    (hBmeas : ∀ u, Measurable (B u)) (V : TBoundedSP (𝓖 := F) T hBmeas) :
    restrictInput ht hBmeas (simpleAssembly_T (𝓖 := F) (μ := μ) T hBmeas V) =
      simpleAssembly_T (𝓖 := F) (μ := μ) t hBmeas (lowerSP T t hBmeas V) := by
  apply Lp.ext
  have hV' : (simpleAssembly_T (𝓖 := F) (μ := μ) T hBmeas V : ℝ≥0 × Ω → ℝ)
      =ᵐ[trimMeasure_T (𝓖 := F) (μ := μ) t hBmeas] Function.uncurry ⇑V.val :=
    ae_mono (trimMeasure_mono ht hBmeas)
      (memLp_uncurry_trim_T (𝓖 := F) (μ := μ) T hBmeas V.val).coeFn_toLp
  have hW' : (simpleAssembly_T (𝓖 := F) (μ := μ) t hBmeas (lowerSP T t hBmeas V) :
      ℝ≥0 × Ω → ℝ) =ᵐ[trimMeasure_T (𝓖 := F) (μ := μ) t hBmeas]
        Function.uncurry ⇑(lowerSP T t hBmeas V).val :=
    (memLp_uncurry_trim_T (𝓖 := F) (μ := μ) t hBmeas (lowerSP T t hBmeas V).val).coeFn_toLp
  filter_upwards [restrictInput_ae ht hBmeas (simpleAssembly_T (𝓖 := F) (μ := μ) T hBmeas V),
    hV', hW', ae_window t hBmeas] with z hr hV hW hz
  rw [hr, hV, hW, lowerSP_val]
  change _ = ⇑(cutSP T t hBmeas V).val z.1 z.2
  rw [cutSP_apply T t hBmeas V hz.1, Prod.mk.eta]
  exact (indicator_of_mem (show z ∈ timeBand t from ⟨hz, mem_univ _⟩) _).symm

theorem restrictPathLp_simple {t T : ℝ≥0} (ht : t ≤ T)
    (hB : ∀ ω, Continuous (fun s => B s ω)) (hBmeas : ∀ u, Measurable (B u))
    (V : TBoundedSP (𝓖 := F) T hBmeas) :
    restrictPathLp ht (boundedSimplePathLp (μ := μ) T hB hBmeas V) =
      boundedSimplePathLp (μ := μ) t hB hBmeas (lowerSP T t hBmeas V) := by
  apply Lp.ext
  have hV' : (boundedSimplePathLp (μ := μ) T hB hBmeas V : Ω → C(Window T, ℝ)) =ᵐ[μ]
      simpleIntegralPath T hB V.val :=
    (simpleIntegralPath_memLp (μ := μ) T hB hBmeas V.val).coeFn_toLp
  have hW' : (boundedSimplePathLp (μ := μ) t hB hBmeas (lowerSP T t hBmeas V) :
      Ω → C(Window t, ℝ)) =ᵐ[μ] simpleIntegralPath t hB (lowerSP T t hBmeas V).val :=
    (simpleIntegralPath_memLp (μ := μ) t hB hBmeas (lowerSP T t hBmeas V).val).coeFn_toLp
  filter_upwards [restrictPathLp_ae ht (boundedSimplePathLp (μ := μ) T hB hBmeas V), hV', hW']
      with ω hr hV hW
  rw [hr, hV, hW]
  apply ContinuousMap.ext
  intro s
  change simpleIntegralPath T hB V.val ω ⟨s.val, s.property.1, s.property.2.trans ht⟩ = _
  rw [simpleIntegralPath_apply, simpleIntegralPath_apply, lowerSP_val,
    cutSP_integral, min_eq_left s.property.2]

/-- Completed integrals on two different horizons commute with restriction. -/
theorem continuousIto_restrict {t T : ℝ≥0} (ht : t ≤ T)
    (hB : ∀ ω, Continuous (fun s => B s ω)) (hBmeas : ∀ u, Measurable (B u))
    (U : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    restrictPathLp ht (continuousIto T hB hBmeas U) =
      continuousIto t hB hBmeas (restrictInput ht hBmeas U) := by
  refine (simpleAssembly_T_denseRange (𝓖 := F) (μ := μ) T hBmeas).induction_on
    (p := fun U => restrictPathLp ht (continuousIto T hB hBmeas U) =
      continuousIto t hB hBmeas (restrictInput ht hBmeas U)) U ?_ ?_
  · exact isClosed_eq
      ((restrictPathLp ht).continuous.comp (continuousIto T hB hBmeas).continuous)
      ((continuousIto t hB hBmeas).continuous.comp (restrictInput ht hBmeas).continuous)
  · intro V
    rw [restrictInput_simple, StoppedContinuousIto.continuousIto_simple,
      StoppedContinuousIto.continuousIto_simple, restrictPathLp_simple]

/-- The restriction identity is simultaneous at all times in the smaller
window; it is not merely equality of terminal values or separate-time laws. -/
theorem continuousIto_restrict_representative {t T : ℝ≥0} (ht : t ≤ T)
    (hB : ∀ ω, Continuous (fun s => B s ω)) (hBmeas : ∀ u, Measurable (B u))
    (U : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    ∀ᵐ ω ∂μ, ∀ s : Window t,
      representative (continuousIto T hB hBmeas U) ω
          ⟨s.val, s.property.1, s.property.2.trans ht⟩ =
        representative (continuousIto t hB hBmeas (restrictInput ht hBmeas U)) ω s := by
  have heq := continuousIto_restrict ht hB hBmeas U
  filter_upwards [restrictPathLp_ae ht (continuousIto T hB hBmeas U),
    representative_ae (continuousIto T hB hBmeas U),
    representative_ae (continuousIto t hB hBmeas (restrictInput ht hBmeas U))]
      with ω hr hT ht'
  rw [heq, ht', hT] at hr
  intro s
  exact (congrArg (fun p : C(Window t, ℝ) => p s) hr).symm

/-- Concrete window integral coherence. Membership at the larger horizon is
produced by bounded continuous adapted coefficients or their null modifications. -/
theorem windowIto_restrict {t T : ℝ≥0} (ht : t ≤ T)
    (hB : ∀ ω, Continuous (fun s => B s ω)) (hBmeas : ∀ u, Measurable (B u))
    (H : ℝ≥0 → Ω → ℝ)
    (hm : MemLp (Function.uncurry H) 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    ∀ᵐ ω ∂μ, ∀ s ≤ t,
      StrongSDEConcreteMaps.windowIto (μ := μ) F T B hB hBmeas H s ω =
        StrongSDEConcreteMaps.windowIto (μ := μ) F t B hB hBmeas H s ω := by
  have hn := hm.mono_measure (trimMeasure_mono ht hBmeas)
  have heq : restrictInput ht hBmeas (hm.toLp (Function.uncurry H)) =
      hn.toLp (Function.uncurry H) := by
    apply Lp.ext
    have h1 : (hm.toLp (Function.uncurry H) : ℝ≥0 × Ω → ℝ)
        =ᵐ[trimMeasure_T (𝓖 := F) (μ := μ) t hBmeas] Function.uncurry H :=
      ae_mono (trimMeasure_mono ht hBmeas) hm.coeFn_toLp
    exact (restrictInput_ae ht hBmeas _).trans (h1.trans hn.coeFn_toLp.symm)
  have hr := continuousIto_restrict_representative ht hB hBmeas
    (hm.toLp (Function.uncurry H))
  rw [heq] at hr
  filter_upwards [hr] with ω hω
  intro s hs
  simpa only [StrongSDEConcreteMaps.windowIto, dif_pos hm, dif_pos hn,
    StrongSDEConcreteMaps.cappedTime, min_eq_left hs, min_eq_left (hs.trans ht)]
    using hω ⟨s, zero_le, hs⟩

end Ripple.Stochastic.HorizonItoRestriction
