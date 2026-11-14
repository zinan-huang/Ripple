import Ripple.Stochastic.ContinuousItoConstruction
import Ripple.Stochastic.FilteredItoIntegralProcessGeneral
import Ripple.Stochastic.DoobContinuous
import Ripple.Stochastic.FilteredItoMartingale

/-!
# Elementary path-valued Itô integrals and their maximal norm estimate

The elementary integrals are measurable as continuous-path
random variables. Doob's inequality supplies their uniform-path L² membership
and the extension bound, without assuming a continuous version for general
integrands.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

namespace Ripple.Stochastic.ContinuousItoElementary
open AdaptedContinuousSpace ContinuousItoConstruction
open FilteredItoIntegralL2 FilteredItoIntegralCLM FilteredItoIntegralProcess
open FilteredItoIntegralProcessGeneral

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
  [IsFilteredPreBrownian B F μ]

/-- Compact windows are nonempty even when the horizon is zero. -/
private theorem window_nonempty (T : ℝ≥0) : Nonempty (Set.Icc (0 : ℝ≥0) T) :=
  ⟨⟨0, zero_le, zero_le⟩⟩

/-- The elementary continuous path is a strongly measurable random variable. -/
theorem simpleIntegralPath_stronglyMeasurable (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ F) : StronglyMeasurable (simpleIntegralPath T hB V) := by
  letI := window_nonempty T
  apply stronglyMeasurable_of_evaluations
  intro t
  have heq : (fun ω => simpleIntegralPath T hB V ω t) =
      itoSimpleProcess hBmeas V t.val :=
    funext fun ω => simpleIntegralPath_apply T hB hBmeas V ω t
  rw [heq]
  have hsum : itoSimpleProcess hBmeas V t.val = fun ω => ∑ p ∈ V.value.support,
      V.value p ω * (B (min p.2 t.val) ω - B (min p.1 t.val) ω) := by
    funext ω
    rw [itoSimpleProcess_apply]
    rfl
  rw [hsum]
  exact Finset.measurable_sum _ fun p _ =>
    ((V.measurable_value p).mono (F.le _) le_rfl).mul ((hBmeas _).sub (hBmeas _))

/-- The square-root formula for the Bochner L² seminorm of a continuous-path variable. -/
theorem eLpNorm_path_two_eq {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (f : Ω → C(K, ℝ)) :
    eLpNorm f 2 μ = (∫⁻ ω, (‖f ω‖₊ : ℝ≥0∞) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  refine lintegral_congr fun ω => ?_
  rw [← ENNReal.rpow_natCast _ 2]
  norm_num
  simp [enorm_eq_nnnorm]

/-- The path norm is literally the running supremum in Doob's inequality. -/
theorem simpleIntegralPath_enorm (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ F) (ω : Ω) :
    (‖simpleIntegralPath T hB V ω‖₊ : ℝ≥0∞) =
      ⨆ t : Set.Icc (0 : ℝ≥0) T,
        (‖itoSimpleProcess hBmeas V t.val ω‖₊ : ℝ≥0∞) := by
  rw [ContinuousMap.nnnorm_eq_iSup_nnnorm, ENNReal.coe_iSup]
  · congr 1
    funext t
    rw [simpleIntegralPath_apply T hB hBmeas]
  · exact ⟨‖simpleIntegralPath T hB V ω‖₊,
      fun _ ⟨t, ht⟩ => ht ▸ (show ‖simpleIntegralPath T hB V ω t‖₊ ≤
        ‖simpleIntegralPath T hB V ω‖₊ from by
          exact_mod_cast (simpleIntegralPath T hB V ω).norm_coe_le_norm t)⟩

/-- Actual path-valued seminorm estimate, supplied by the continuous-time Doob producer. -/
theorem simpleIntegralPath_eLpNorm_le (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ F) :
    eLpNorm (simpleIntegralPath T hB V) 2 μ ≤
      2 * eLpNorm (itoSimpleProcess hBmeas V T) 2 μ := by
  have hc : ∀ ω, Continuous (fun t => itoSimpleProcess hBmeas V t ω) := by
    intro ω
    have hformula : (fun t => itoSimpleProcess hBmeas V t ω) =
        fun t => ∑ p ∈ V.value.support,
          V.value p ω * (B (min p.2 t) ω - B (min p.1 t) ω) := by
      funext t
      rw [itoSimpleProcess_apply]
      rfl
    rw [hformula]
    exact continuous_finset_sum _ fun p _ => continuous_const.mul
      (((hB ω).comp (continuous_const.min continuous_id)).sub
        ((hB ω).comp (continuous_const.min continuous_id)))
  have hd := Doob.lintegral_iSup_sq_le_of_nnreal_continuous_martingale
    (itoSimpleProcess_isMartingale (μ := μ) hBmeas V) T (ae_of_all _ hc)
  have hb : (∫⁻ ω, (‖simpleIntegralPath T hB V ω‖₊ : ℝ≥0∞) ^ 2 ∂μ) ≤
      4 * ∫⁻ ω, (‖itoSimpleProcess hBmeas V T ω‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
    simpa only [simpleIntegralPath_enorm T hB hBmeas V] using hd
  rw [eLpNorm_path_two_eq, Doob.eLpNorm_two_eq]
  have hroot := ENNReal.rpow_le_rpow hb (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hfour : (4 : ℝ≥0∞) ^ ((1 : ℝ) / 2) = 2 := by
    calc (4 : ℝ≥0∞) ^ ((1 : ℝ) / 2)
        = ((2 : ℝ≥0∞) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by norm_num
      _ = 2 := by rw [← ENNReal.rpow_mul]; norm_num
  rwa [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hfour] at hroot

/-- Doob and the terminal L² membership prove the missing Bochner path L² membership. -/
theorem simpleIntegralPath_memLp (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ F) : MemLp (simpleIntegralPath T hB V) 2 μ := by
  refine ⟨(simpleIntegralPath_stronglyMeasurable T hB hBmeas V).aestronglyMeasurable, ?_⟩
  exact (simpleIntegralPath_eLpNorm_le (μ := μ) T hB hBmeas V).trans_lt
    (ENNReal.mul_lt_top (by norm_num) (memLp_itoSimpleProcess (μ := μ) hBmeas V T).2)

/-- Restrict the concrete finite-sum path construction to T-bounded simple processes. -/
def boundedSimplePathLM (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t)) :
    TBoundedSP (𝓖 := F) T hBmeas →ₗ[ℝ] Ω → C(Set.Icc (0 : ℝ≥0) T, ℝ) :=
  (simplePathLM T hB hBmeas).comp (TBoundedSP (𝓖 := F) T hBmeas).subtype

/-- The concrete elementary path-valued L² map. -/
def boundedSimplePathLp (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t)) :
    TBoundedSP (𝓖 := F) T hBmeas →ₗ[ℝ] PathLp (Set.Icc (0 : ℝ≥0) T) μ :=
  elementaryPathLM (boundedSimplePathLM T hB hBmeas)
    (fun V => simpleIntegralPath_memLp T hB hBmeas V.val)

/-- The exact norm estimate consumed by the continuous integral extension. -/
theorem boundedSimplePathLp_norm_le (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (V : TBoundedSP (𝓖 := F) T hBmeas) :
    ‖boundedSimplePathLp (μ := μ) T hB hBmeas V‖ ≤
      2 * ‖simpleAssembly_T (𝓖 := F) (μ := μ) T hBmeas V‖ := by
  have hs := simpleIntegralPath_eLpNorm_le (μ := μ) T hB hBmeas V.val
  have hfin : 2 * eLpNorm (itoSimpleProcess hBmeas V.val T) 2 μ ≠ ⊤ :=
    (ENNReal.mul_lt_top (by norm_num) (memLp_itoSimpleProcess (μ := μ) hBmeas V.val T).2).ne
  have hnorm := ENNReal.toReal_mono hfin hs
  change ‖(simpleIntegralPath_memLp (μ := μ) T hB hBmeas V.val).toLp _‖ ≤ _
  rw [Lp.norm_toLp]
  have hterm : itoSimpleProcess hBmeas V.val T = itoSimple hBmeas V.val :=
    itoSimpleProcess_eq_itoSimple hBmeas V.val V.property
  rw [ENNReal.toReal_mul] at hnorm
  norm_num only [ENNReal.toReal_ofNat] at hnorm
  rw [hterm] at hnorm
  have hiso := assembly_isometry_T (𝓖 := F) (μ := μ) T hBmeas V
  change ‖itoSimpleLp hBmeas V.val‖ =
    ‖simpleAssembly_T (𝓖 := F) (μ := μ) T hBmeas V‖ at hiso
  rw [itoSimpleLp, Lp.norm_toLp] at hiso
  exact hnorm.trans_eq (by rw [hiso])

/-- Evaluation of the concrete elementary path agrees with the existing slice CLM. -/
theorem boundedSimplePathLp_eval (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (V : TBoundedSP (𝓖 := F) T hBmeas) (t : Set.Icc (0 : ℝ≥0) T) :
    itoProcessCLM (𝓖 := F) (μ := μ) T t.val hBmeas
        (simpleAssembly_T (𝓖 := F) (μ := μ) T hBmeas V) =
      evalLp t (boundedSimplePathLp (μ := μ) T hB hBmeas V) := by
  rw [itoProcessCLM_simpleAssembly_T]
  apply Lp.ext
  have hp : (boundedSimplePathLp (μ := μ) T hB hBmeas V : Ω → C(Set.Icc (0 : ℝ≥0) T, ℝ))
      =ᵐ[μ] simpleIntegralPath T hB V.val :=
    (simpleIntegralPath_memLp (μ := μ) T hB hBmeas V.val).coeFn_toLp
  filter_upwards [(evalLp_ae t (boundedSimplePathLp (μ := μ) T hB hBmeas V)), hp,
    (memLp_itoSimpleProcess (μ := μ) hBmeas V.val t.val).coeFn_toLp] with ω he hpω hi
  unfold itoSimpleProcessLp
  rw [hi, he, hpω]
  exact (simpleIntegralPath_apply T hB hBmeas V.val ω t).symm

/-- The concrete continuous Itô CLM, using the installed predictable L² domain. -/
def continuousIto (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t)) :
    Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) →L[ℝ]
      PathLp (Set.Icc (0 : ℝ≥0) T) μ :=
  continuousIntegralCLM (simpleAssembly_T (𝓖 := F) (μ := μ) T hBmeas)
    (boundedSimplePathLM T hB hBmeas)
    (fun V => simpleIntegralPath_memLp T hB hBmeas V.val)

/-- The desired uniform path L² estimate for every predictable integrand. -/
theorem continuousIto_norm_le (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    ‖continuousIto T hB hBmeas φ‖ ≤ 2 * ‖φ‖ :=
  continuousIntegral_norm_le _ (simpleAssembly_T_denseRange T hBmeas) _ _
    (boundedSimplePathLp_norm_le T hB hBmeas) φ

/-- The constructed continuous path integral agrees at every fixed time with
Ripple's existing L² slice integral. -/
theorem continuousIto_eval (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (t : Set.Icc (0 : ℝ≥0) T) :
    evalLp t (continuousIto T hB hBmeas φ) =
      itoProcessCLM (𝓖 := F) (μ := μ) T t.val hBmeas φ := by
  exact continuousIntegral_eval_eq _ (simpleAssembly_T_denseRange T hBmeas) _ _
    (boundedSimplePathLp_norm_le T hB hBmeas)
    (fun t => itoProcessCLM (𝓖 := F) (μ := μ) T t.val hBmeas)
    (fun t V => boundedSimplePathLp_eval T hB hBmeas V t) φ t

/-- The concrete continuous integral lies in the closed adapted S² space. -/
theorem continuousIto_mem_adapted (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    continuousIto T hB hBmeas φ ∈ adaptedSubmodule (fun t : Set.Icc (0 : ℝ≥0) T => F t.val) := by
  apply (mem_adaptedSubmodule _ _).mpr
  intro t
  rw [continuousIto_eval T hB hBmeas φ t]
  exact mem_lpMeas_iff_aestronglyMeasurable.mpr
    (itoProcessCLM_aeStronglyMeasurable (𝓖 := F) T t.val hBmeas φ)

/-- Null-set completeness yields an exactly adapted continuous realization. -/
theorem continuousIto_representative_adapted (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (t : Set.Icc (0 : ℝ≥0) T) :
    StronglyMeasurable[F t.val]
      (fun ω => representative (continuousIto T hB hBmeas φ) ω t) :=
  representative_adapted (fun t : Set.Icc (0 : ℝ≥0) T => F t.val)
    (fun t => hnull t.val)
    ⟨continuousIto T hB hBmeas φ, continuousIto_mem_adapted T hB hBmeas φ⟩ t

/-- The chosen continuous representative is a martingale on the window when
the prescribed filtration absorbs ambient measurable null sets. -/
theorem continuousIto_representative_isMartingale (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    Martingale (fun (t : Set.Icc (0 : ℝ≥0) T) ω =>
        representative (continuousIto T hB hBmeas φ) ω t)
      (Doob.Filtration.compMono mΩ F (fun t : Set.Icc (0 : ℝ≥0) T => t.val)
        (fun _ _ h => h)) μ := by
  have hm := Doob.martingale_compMono
    (itoIntegralProcess_isMartingale (𝓖 := F) T hBmeas φ)
    (fun t : Set.Icc (0 : ℝ≥0) T => t.val) (fun _ _ h => h)
  have heq : ∀ t : Set.Icc (0 : ℝ≥0) T,
      (fun ω => representative (continuousIto T hB hBmeas φ) ω t) =ᵐ[μ]
        itoIntegralProcess (𝓖 := F) T hBmeas φ t.val := by
    intro t
    have he := evalLp_ae t (continuousIto T hB hBmeas φ)
    rw [continuousIto_eval T hB hBmeas φ t] at he
    have hrep : (fun ω => (continuousIto T hB hBmeas φ : Ω → C(Set.Icc (0 : ℝ≥0) T, ℝ)) ω t)
        =ᵐ[μ] fun ω => representative (continuousIto T hB hBmeas φ) ω t :=
      (representative_indistinguishable (continuousIto T hB hBmeas φ)).mono fun ω hω => hω t
    exact (hrep.symm.trans he.symm).trans
      (itoIntegralProcess_ae_eq_itoProcessCLM (𝓖 := F) T t.val hBmeas φ).symm
  refine ⟨fun t => continuousIto_representative_adapted T hB hBmeas hnull φ t, ?_⟩
  intro s t hst
  exact (condExp_congr_ae (heq t)).trans ((hm.2 s t hst).trans (heq s).symm)

/-- A continuous version is now constructed from Brownian continuity and Doob,
with no general-integrand regularity or completeness premise. -/
theorem exists_continuousIto_modification (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    ∃ X : Set.Icc (0 : ℝ≥0) T → Ω → ℝ,
      (∀ ω, Continuous (fun t => X t ω)) ∧
      (∀ t, X t =ᵐ[μ] (itoProcessCLM (𝓖 := F) (μ := μ) T t.val hBmeas φ : Ω → ℝ)) ∧
      MemLp (fun ω => representative (continuousIto T hB hBmeas φ) ω) 2 μ := by
  refine ⟨fun t ω => representative (continuousIto T hB hBmeas φ) ω t,
    fun ω => (representative (continuousIto T hB hBmeas φ) ω).continuous, ?_,
    representative_memLp _⟩
  intro t
  have he := evalLp_ae t (continuousIto T hB hBmeas φ)
  rw [continuousIto_eval T hB hBmeas φ t] at he
  have hrep : (fun ω => (continuousIto T hB hBmeas φ : Ω → C(Set.Icc (0 : ℝ≥0) T, ℝ)) ω t)
      =ᵐ[μ] fun ω => representative (continuousIto T hB hBmeas φ) ω t :=
    (representative_indistinguishable (continuousIto T hB hBmeas φ)).mono fun ω hω => hω t
  exact hrep.symm.trans he.symm

end Ripple.Stochastic.ContinuousItoElementary
