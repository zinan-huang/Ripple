import Ripple.Stochastic.ContinuousItoElementary
import Ripple.Stochastic.BoundedPredictableApproximation
import Ripple.Stochastic.FilteredItoIntegralProcessIsometry

/-!
# Deterministic stopping of the actual continuous Itô integral

Multiplication by the predictable band indicator is an
endomorphism of the installed predictable L² space. An explicit clipping of
elementary cells proves the stopping identity before passing through the
installed dense simple-process embedding. No continuity of the clipped
integrand is required.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace Ripple.Stochastic.StoppedContinuousIto
open AdaptedContinuousSpace ContinuousItoConstruction ContinuousItoElementary
open FilteredItoIntegralL2 FilteredItoIntegralCLM FilteredItoIntegralProcess
open FilteredItoIntegralProcessGeneral BoundedPredictableApproximation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
  [IsFilteredPreBrownian B F μ]

abbrev Window (T : ℝ≥0) := Icc (0 : ℝ≥0) T

def timeBand (t : ℝ≥0) : Set (ℝ≥0 × Ω) := Ioc 0 t ×ˢ univ

theorem timeBand_measurable (t : ℝ≥0) : MeasurableSet[F.predictable] (timeBand t) :=
  measurableSet_predictable_Ioc_prod (𝓕 := F) 0 t MeasurableSet.univ

/-- Time clipping preserves membership in the very same predictable L² domain. -/
theorem timeCut_memLp (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (U : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    MemLp ((timeBand t).indicator (U : ℝ≥0 × Ω → ℝ)) 2
      (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) :=
  (Lp.memLp U).indicator (timeBand_measurable t)

/-- The predictable band projection is continuous and has norm at most one. -/
def timeCut (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u)) :
    Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) →L[ℝ]
      Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) :=
  LinearMap.mkContinuous
    { toFun := fun U => (timeCut_memLp T t hBmeas U).toLp _
      map_add' := fun U V => by
        apply Lp.ext
        filter_upwards [(timeCut_memLp T t hBmeas (U + V)).coeFn_toLp,
          Lp.coeFn_add ((timeCut_memLp T t hBmeas U).toLp _)
            ((timeCut_memLp T t hBmeas V).toLp _),
          (timeCut_memLp T t hBmeas U).coeFn_toLp,
          (timeCut_memLp T t hBmeas V).coeFn_toLp,
          Lp.coeFn_add U V] with z hsum hadd hU hV huv
        rw [hsum, hadd, Pi.add_apply, hU, hV]
        by_cases h : z ∈ timeBand t
        · rw [indicator_of_mem h, indicator_of_mem h, indicator_of_mem h, huv, Pi.add_apply]
        · rw [indicator_of_notMem h, indicator_of_notMem h, indicator_of_notMem h, add_zero]
      map_smul' := fun c U => by
        apply Lp.ext
        filter_upwards [(timeCut_memLp T t hBmeas (c • U)).coeFn_toLp,
          Lp.coeFn_smul c ((timeCut_memLp T t hBmeas U).toLp _),
          (timeCut_memLp T t hBmeas U).coeFn_toLp,
          Lp.coeFn_smul c U] with z hsmul hadd hU hcu
        rw [hsmul, RingHom.id_apply, hadd, Pi.smul_apply, hU]
        by_cases h : z ∈ timeBand t
        · rw [indicator_of_mem h, indicator_of_mem h, hcu, Pi.smul_apply]
        · rw [indicator_of_notMem h, indicator_of_notMem h, smul_zero] }
    1 (fun U => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [one_mul, Lp.norm_toLp, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.memLp U).2.ne (eLpNorm_indicator_le _))

theorem timeCut_ae (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (U : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    (timeCut T t hBmeas U : ℝ≥0 × Ω → ℝ) =ᵐ[trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas]
      (timeBand t).indicator (U : ℝ≥0 × Ω → ℝ) :=
  (timeCut_memLp T t hBmeas U).coeFn_toLp

theorem timeCut_norm_le (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (U : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    ‖timeCut T t hBmeas U‖ ≤ ‖U‖ := by
  change ‖(timeCut_memLp T t hBmeas U).toLp _‖ ≤ _
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp U).2.ne (eLpNorm_indicator_le _)

/-- The clipped norm is the local energy, with no terminal-time enlargement. -/
theorem timeCut_norm_sq (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (U : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    ‖timeCut T t hBmeas U‖ ^ 2 =
      ∫ z in timeBand t, (U z) ^ 2
        ∂(trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) := by
  rw [lp_two_norm_sq, ← integral_indicator (timeBand_measurable (F := F) t)]
  apply integral_congr_ae
  filter_upwards [timeCut_ae T t hBmeas U] with z hz
  rw [hz]
  by_cases h : z ∈ timeBand t
  · rw [indicator_of_mem h, indicator_of_mem h]
  · rw [indicator_of_notMem h, indicator_of_notMem h]
    norm_num

/-- A continuous path stopped at a deterministic time remains in the same window. -/
def stopTime (T t : ℝ≥0) (s : Window T) : Window T :=
  ⟨min s.val t, zero_le, (min_le_left _ _).trans s.property.2⟩

theorem stopTime_continuous (T t : ℝ≥0) : Continuous (stopTime T t) :=
  (continuous_subtype_val.min continuous_const).subtype_mk _

def stopPath (T t : ℝ≥0) : C(Window T, ℝ) →L[ℝ] C(Window T, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun s => x (stopTime T t s),
        x.continuous.comp (stopTime_continuous T t)⟩
      map_add' := fun x y => by ext s; rfl
      map_smul' := fun c x => by ext s; rfl }
    1 (fun x => by
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg x)).mpr
      intro s
      exact x.norm_coe_le_norm (stopTime T t s))

@[simp] theorem stopPath_apply (T t : ℝ≥0) (x : C(Window T, ℝ)) (s : Window T) :
    stopPath T t x s = x (stopTime T t s) := rfl

def stopPathLp (T t : ℝ≥0) : PathLp (Window T) μ →L[ℝ] PathLp (Window T) μ :=
  (stopPath T t).compLpL 2 μ

theorem stopPathLp_ae (T t : ℝ≥0) (X : PathLp (Window T) μ) :
    (stopPathLp T t X : Ω → C(Window T, ℝ)) =ᵐ[μ] fun ω => stopPath T t (X ω) :=
  (stopPath T t).coeFn_compLpL X

private theorem sum_sp_apply {ι : Type*} {T : ℝ≥0} {hBmeas : ∀ u, Measurable (B u)}
    (s : Finset ι)
    (V : ι → TBoundedSP (𝓖 := F) T hBmeas) (u : ℝ≥0) (ω : Ω) :
    ⇑(∑ i ∈ s, V i).val u ω = ∑ i ∈ s, ⇑(V i).val u ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, Submodule.coe_add, SimpleProcess.coe_add,
      Pi.add_apply, ih]

private theorem sum_sp_integral {ι : Type*} {T : ℝ≥0} {hBmeas : ∀ u, Measurable (B u)}
    (s : Finset ι)
    (V : ι → TBoundedSP (𝓖 := F) T hBmeas) (u : ℝ≥0) (ω : Ω) :
    itoSimpleProcess hBmeas (∑ i ∈ s, V i).val u ω =
      ∑ i ∈ s, itoSimpleProcess hBmeas (V i).val u ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [itoSimpleProcess, SimpleProcess.integral]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, Submodule.coe_add, itoSimpleProcess_add,
      Pi.add_apply, ih]

/-- Clip one elementary interval, discarding it if its left endpoint is too late. -/
def cutCell (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : TBoundedSP (𝓖 := F) T hBmeas) (p : ℝ≥0 × ℝ≥0) :
    TBoundedSP (𝓖 := F) T hBmeas :=
  if hp : p ∈ V.val.value.support then
    if h : p.1 ≤ t then
      stepSP hBmeas (le_min (V.val.le_of_mem_support_value p hp) h)
        ((min_le_left _ _).trans (V.property p hp)) (V.val.measurable_value p)
        (fun ω => by simpa only [Real.norm_eq_abs] using V.val.value_le_valueBound p ω)
    else 0
  else 0

/-- The explicit elementary clipping uses precisely the installed elementary type. -/
def cutSP (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : TBoundedSP (𝓖 := F) T hBmeas) : TBoundedSP (𝓖 := F) T hBmeas :=
  ∑ p ∈ V.val.value.support, cutCell T t hBmeas V p

private theorem cutCell_apply (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : TBoundedSP (𝓖 := F) T hBmeas) (p : ℝ≥0 × ℝ≥0)
    (hp : p ∈ V.val.value.support) (u : ℝ≥0) (ω : Ω) :
    ⇑(cutCell T t hBmeas V p).val u ω =
      (Ioc p.1 (min p.2 t)).indicator (fun _ => V.val.value p ω) u := by
  classical
  by_cases h : p.1 ≤ t
  · simp only [cutCell, dif_pos hp, dif_pos h]
    rw [SimpleProcess.apply_eq]
    simp [stepSP, Finsupp.sum_single_index]
  · rw [cutCell, dif_pos hp, dif_neg h]
    have h_empty : Ioc p.1 (min p.2 t) = ∅ :=
      Ioc_eq_empty (not_lt.mpr ((min_le_right _ _).trans (not_le.mp h).le))
    simp [h_empty]

/-- Positive-time clipping is literal multiplication by the band indicator. -/
theorem cutSP_apply (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : TBoundedSP (𝓖 := F) T hBmeas) {u : ℝ≥0} (hu : 0 < u) (ω : Ω) :
    ⇑(cutSP T t hBmeas V).val u ω =
      (timeBand t).indicator (Function.uncurry ⇑V.val) (u, ω) := by
  classical
  rw [cutSP, sum_sp_apply]
  have hc : ∀ p ∈ V.val.value.support,
      ⇑(cutCell T t hBmeas V p).val u ω =
        (Ioc p.1 (min p.2 t)).indicator (fun _ => V.val.value p ω) u :=
    fun p hp => cutCell_apply T t hBmeas V p hp u ω
  rw [Finset.sum_congr rfl hc]
  by_cases hut : u ≤ t
  · rw [indicator_of_mem (show (u, ω) ∈ timeBand t from ⟨⟨hu, hut⟩, mem_univ _⟩)]
    change (∑ p ∈ V.val.value.support, _) = ⇑V.val u ω
    rw [SimpleProcess.apply_eq]
    have hbot : u ∉ ({⊥} : Set ℝ≥0) := by
      intro hmem
      rw [mem_singleton_iff] at hmem
      subst hmem
      exact not_lt_bot hu
    simp only [indicator_of_notMem hbot, zero_add, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hpu : u ∈ Ioc p.1 p.2
    · rw [indicator_of_mem hpu, indicator_of_mem
        (show u ∈ Ioc p.1 (min p.2 t) from ⟨hpu.1, le_min hpu.2 hut⟩)]
    · rw [indicator_of_notMem hpu, indicator_of_notMem (show u ∉ Ioc p.1 (min p.2 t) by
        intro hmem; exact hpu ⟨hmem.1, hmem.2.trans (min_le_left _ _)⟩)]
  · rw [indicator_of_notMem (by intro hmem; exact hut hmem.1.2)]
    apply Finset.sum_eq_zero
    intro p hp
    apply indicator_of_notMem
    intro hmem
    exact hut (hmem.2.trans (min_le_right _ _))

/-- Elementary stochastic integration commutes with this clipping at every sample. -/
theorem cutSP_integral (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : TBoundedSP (𝓖 := F) T hBmeas) (u : ℝ≥0) (ω : Ω) :
    itoSimpleProcess hBmeas (cutSP T t hBmeas V).val u ω =
      itoSimpleProcess hBmeas V.val (min u t) ω := by
  classical
  rw [cutSP, sum_sp_integral, itoSimpleProcess_apply, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : p.1 ≤ t
  · simp only [cutCell, dif_pos hp, dif_pos h]
    rw [itoSimpleProcess_stepSP]
    have he : min p.1 (min u t) = min p.1 u := by
      rw [min_left_comm, min_eq_left h, min_comm]
    rw [he]
    congr 2
    exact congrArg (fun v => B v ω) (by simp only [min_assoc, min_left_comm, min_comm])
  · rw [cutCell, dif_pos hp, dif_neg h]
    have hlo : min u t ≤ p.1 := (min_le_right _ _).trans (not_le.mp h).le
    have hhi : min u t ≤ p.2 := hlo.trans (V.val.le_of_mem_support_value p hp)
    simp [itoSimpleProcess, SimpleProcess.integral, min_eq_right hlo, min_eq_right hhi]

/-- The predictable L² band projection agrees with elementary cell clipping. -/
theorem timeCut_simpleAssembly (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : TBoundedSP (𝓖 := F) T hBmeas) :
    timeCut T t hBmeas (simpleAssembly_T (𝓖 := F) (μ := μ) T hBmeas V) =
      simpleAssembly_T (𝓖 := F) (μ := μ) T hBmeas (cutSP T t hBmeas V) := by
  apply Lp.ext
  filter_upwards [timeCut_ae T t hBmeas (simpleAssembly_T (𝓖 := F) T hBmeas V),
    (memLp_uncurry_trim_T (𝓖 := F) T hBmeas V.val).coeFn_toLp,
    (memLp_uncurry_trim_T (𝓖 := F) T hBmeas (cutSP T t hBmeas V).val).coeFn_toLp,
    ae_window T hBmeas] with z hcut hV hW hz
  have hV' : (simpleAssembly_T (𝓖 := F) (μ := μ) T hBmeas V : ℝ≥0 × Ω → ℝ) z =
      Function.uncurry ⇑V.val z := hV
  have hW' : (simpleAssembly_T (𝓖 := F) (μ := μ) T hBmeas (cutSP T t hBmeas V) :
      ℝ≥0 × Ω → ℝ) z = Function.uncurry ⇑(cutSP T t hBmeas V).val z := hW
  rw [hcut, hW']
  change _ = ⇑(cutSP T t hBmeas V).val z.1 z.2
  rw [cutSP_apply T t hBmeas V hz.1, Prod.mk.eta]
  by_cases h : z ∈ timeBand t
  · rw [indicator_of_mem h, indicator_of_mem h, hV']
  · rw [indicator_of_notMem h, indicator_of_notMem h]

/-- Agreement with the elementary path map, in the exact installed path quotient. -/
theorem continuousIto_simple (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ u, Measurable (B u))
    (V : TBoundedSP (𝓖 := F) T hBmeas) :
    continuousIto T hB hBmeas (simpleAssembly_T (𝓖 := F) (μ := μ) T hBmeas V) =
      boundedSimplePathLp T hB hBmeas V :=
  continuousIntegral_simple _ (simpleAssembly_T_denseRange T hBmeas) _ _
    (boundedSimplePathLp_norm_le T hB hBmeas) V

/-- Stopping of elementary continuous integrals, as an identity of path L² classes. -/
theorem boundedSimplePathLp_cut (T t : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ u, Measurable (B u))
    (V : TBoundedSP (𝓖 := F) T hBmeas) :
    boundedSimplePathLp (μ := μ) T hB hBmeas (cutSP T t hBmeas V) =
      stopPathLp T t (boundedSimplePathLp (μ := μ) T hB hBmeas V) := by
  apply Lp.ext
  have hcutp : (boundedSimplePathLp (μ := μ) T hB hBmeas (cutSP T t hBmeas V) :
      Ω → C(Window T, ℝ)) =ᵐ[μ] simpleIntegralPath T hB (cutSP T t hBmeas V).val :=
    (simpleIntegralPath_memLp (μ := μ) T hB hBmeas (cutSP T t hBmeas V).val).coeFn_toLp
  have hVp : (boundedSimplePathLp (μ := μ) T hB hBmeas V : Ω → C(Window T, ℝ)) =ᵐ[μ]
      simpleIntegralPath T hB V.val :=
    (simpleIntegralPath_memLp (μ := μ) T hB hBmeas V.val).coeFn_toLp
  filter_upwards [hcutp, stopPathLp_ae T t (boundedSimplePathLp (μ := μ) T hB hBmeas V),
    hVp] with ω hcut hstop hV
  rw [hcut, hstop, hV]
  apply ContinuousMap.ext
  intro s
  rw [stopPath_apply, simpleIntegralPath_apply T hB hBmeas,
    simpleIntegralPath_apply T hB hBmeas]
  exact cutSP_integral T t hBmeas V s.val ω

/-- The actual completed continuous Itô map commutes with deterministic stopping. -/
theorem continuousIto_timeCut (T t : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ u, Measurable (B u))
    (U : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    continuousIto T hB hBmeas (timeCut T t hBmeas U) =
      stopPathLp T t (continuousIto T hB hBmeas U) := by
  refine (simpleAssembly_T_denseRange (𝓖 := F) (μ := μ) T hBmeas).induction_on
    (p := fun U => continuousIto T hB hBmeas (timeCut T t hBmeas U) =
      stopPathLp T t (continuousIto T hB hBmeas U)) U ?_ ?_
  · exact isClosed_eq
      ((continuousIto T hB hBmeas).continuous.comp (timeCut T t hBmeas).continuous)
      ((stopPathLp T t).continuous.comp (continuousIto T hB hBmeas).continuous)
  · intro V
    rw [timeCut_simpleAssembly, continuousIto_simple, continuousIto_simple]
    exact boundedSimplePathLp_cut T t hB hBmeas V

/-- One common null event gives the stopping identity simultaneously at all times. -/
theorem continuousIto_timeCut_representative (T t : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ u, Measurable (B u))
    (U : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    ∀ᵐ ω ∂μ, ∀ s : Window T,
      representative (continuousIto T hB hBmeas (timeCut T t hBmeas U)) ω s =
        representative (continuousIto T hB hBmeas U) ω (stopTime T t s) := by
  have heq := continuousIto_timeCut T t hB hBmeas U
  filter_upwards [representative_ae (continuousIto T hB hBmeas (timeCut T t hBmeas U)),
    representative_ae (continuousIto T hB hBmeas U),
    stopPathLp_ae T t (continuousIto T hB hBmeas U)] with ω hc hU hs
  intro s
  rw [← hc, heq, hs, hU]
  rfl

/-- Local Doob bound for the actual stopped integral, in the genuine path norm. -/
theorem stopped_continuousIto_norm_sq_le (T t : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ u, Measurable (B u))
    (U : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    ‖stopPathLp T t (continuousIto T hB hBmeas U)‖ ^ 2 ≤
      4 * ∫ z in timeBand t, (U z) ^ 2
        ∂(trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) := by
  rw [← continuousIto_timeCut T t hB hBmeas U, ← timeCut_norm_sq T t hBmeas U]
  have h := continuousIto_norm_le T hB hBmeas (timeCut T t hBmeas U)
  nlinarith [norm_nonneg (continuousIto T hB hBmeas (timeCut T t hBmeas U)),
    norm_nonneg (timeCut T t hBmeas U)]

end Ripple.Stochastic.StoppedContinuousIto
