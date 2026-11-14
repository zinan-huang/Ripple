import Ripple.Stochastic.BoundedPredictableApproximation
import Ripple.Stochastic.ContinuousIntegralVersion

/-!
# Deterministic restriction of elementary Itô integrals

The restricted predictable measure and the truncated elementary integrand are
constructed from the installed definitions. Elementary consistency is pointwise
before passing to the installed continuous representatives.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal

namespace Ripple.Stochastic.ContinuousItoConsistency
open FilteredItoIntegralCLM FilteredItoIntegralProcess
open FilteredItoIntegralProcessGeneral ContinuousItoElementary
open BoundedPredictableApproximation AdaptedContinuousSpace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
  [IsFilteredPreBrownian B F μ]

/-- Restriction to a smaller deterministic band is exactly the installed measure. -/
theorem trimMeasure_restrict {T S : ℝ≥0} (hTS : T ≤ S)
    (hBmeas : ∀ t, Measurable (B t)) :
    (trimMeasure_T (𝓖 := F) (μ := μ) S hBmeas).restrict
        (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)) =
      trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas := by
  rw [trimMeasure_T_eq_restrict (𝓖 := F) S hBmeas,
    Measure.restrict_restrict_of_subset
      (Set.prod_mono (Set.Ioc_subset_Ioc le_rfl hTS) subset_rfl),
    trimMeasure_T_eq_restrict (𝓖 := F) T hBmeas]

/-- An installed predictable L² integrand remains in that class on a smaller horizon. -/
theorem memLp_restrictIntegrand {T S : ℝ≥0} (hTS : T ≤ S)
    (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) S hBmeas)) :
    MemLp (φ : ℝ≥0 × Ω → ℝ) 2
      (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) := by
  rw [← trimMeasure_restrict hTS hBmeas]
  exact (Lp.memLp φ).restrict _

/-- Actual restriction of an integrand, with no consistency law supplied as data. -/
def restrictIntegrand {T S : ℝ≥0} (hTS : T ≤ S)
    (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) S hBmeas)) :
    Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) :=
  (memLp_restrictIntegrand hTS hBmeas φ).toLp (φ : ℝ≥0 × Ω → ℝ)

/-- The restriction constructor preserves the integrand on the smaller measure. -/
theorem restrictIntegrand_ae {T S : ℝ≥0} (hTS : T ≤ S)
    (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) S hBmeas)) :
    (restrictIntegrand hTS hBmeas φ : ℝ≥0 × Ω → ℝ) =ᵐ[
      trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas] (φ : ℝ≥0 × Ω → ℝ) :=
  (memLp_restrictIntegrand hTS hBmeas φ).coeFn_toLp

/-- Transfer an almost-everywhere assertion from a larger horizon to a smaller one. -/
theorem ae_of_horizon_le {T S : ℝ≥0} (hTS : T ≤ S)
    (hBmeas : ∀ t, Measurable (B t)) {p : ℝ≥0 × Ω → Prop}
    (hp : ∀ᵐ z ∂(trimMeasure_T (𝓖 := F) (μ := μ) S hBmeas), p z) :
    ∀ᵐ z ∂(trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas), p z := by
  rw [← trimMeasure_restrict hTS hBmeas]
  exact ae_restrict_of_ae hp

/-- Restriction is a contraction between the actual predictable L² spaces. -/
def restrictIntegrandCLM {T S : ℝ≥0} (hTS : T ≤ S)
    (hBmeas : ∀ t, Measurable (B t)) :
    Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) S hBmeas) →L[ℝ]
      Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) :=
  LinearMap.mkContinuous
    { toFun := restrictIntegrand hTS hBmeas
      map_add' := fun φ ψ => by
        apply Lp.ext
        filter_upwards [restrictIntegrand_ae hTS hBmeas (φ + ψ),
          restrictIntegrand_ae hTS hBmeas φ, restrictIntegrand_ae hTS hBmeas ψ,
          ae_of_horizon_le hTS hBmeas (Lp.coeFn_add φ ψ),
          Lp.coeFn_add (restrictIntegrand hTS hBmeas φ)
            (restrictIntegrand hTS hBmeas ψ)] with z hs hφ hψ ha hr
        rw [hs, ha, hr]
        simp only [Pi.add_apply, hφ, hψ]
      map_smul' := fun c φ => by
        apply Lp.ext
        filter_upwards [restrictIntegrand_ae hTS hBmeas (c • φ),
          restrictIntegrand_ae hTS hBmeas φ,
          ae_of_horizon_le hTS hBmeas (Lp.coeFn_smul c φ),
          Lp.coeFn_smul c (restrictIntegrand hTS hBmeas φ)] with z hs hφ ha hr
        rw [RingHom.id_apply, hs, ha, hr]
        simp only [Pi.smul_apply, hφ] }
    1 (fun φ => by
      change ‖(memLp_restrictIntegrand hTS hBmeas φ).toLp _‖ ≤ 1 * ‖φ‖
      rw [one_mul, Lp.norm_toLp, Lp.norm_def]
      apply ENNReal.toReal_mono (Lp.memLp φ).2.ne
      apply eLpNorm_mono_measure
      rw [← trimMeasure_restrict hTS hBmeas]
      exact Measure.restrict_le_self)

/-- Keep the coefficient adapted at its original left endpoint, shorten the
right endpoint, and discard cells lying entirely after the horizon. -/
def truncateCell (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ F) (p : ℝ≥0 × ℝ≥0) :
    TBoundedSP (𝓖 := F) T hBmeas := by
  classical
  exact if h : p.1 ≤ p.2 ∧ p.1 ≤ T then
    stepSP hBmeas (le_min h.1 h.2) (min_le_right _ _)
      (V.measurable_value p)
      (fun ω => by simpa only [Real.norm_eq_abs] using V.value_le_valueBound p ω)
  else 0

/-- Deterministic truncation is a finite sum of installed predictable cells. -/
def truncateSimple (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ F) : TBoundedSP (𝓖 := F) T hBmeas := by
  classical
  exact ∑ p ∈ V.value.support, truncateCell T hBmeas V p

/-- A linear map makes finite-sum evaluation of elementary stochastic integrals explicit. -/
def simpleIntegralLM (hBmeas : ∀ t, Measurable (B t)) (t : ℝ≥0) :
    SimpleProcess ℝ F →ₗ[ℝ] (Ω → ℝ) where
  toFun V := itoSimpleProcess hBmeas V t
  map_add' V W := itoSimpleProcess_add hBmeas V W t
  map_smul' c V := itoSimpleProcess_smul hBmeas c V t

/-- Evaluation of an elementary integrand is linear. -/
def simpleValueLM (t : ℝ≥0) (ω : Ω) : SimpleProcess ℝ F →ₗ[ℝ] ℝ where
  toFun V := V t ω
  map_add' V W := by simp only [SimpleProcess.coe_add, Pi.add_apply]
  map_smul' c V := by
    simp only [SimpleProcess.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

/-- Deterministic truncation does not change any elementary stochastic integral
at a time in the shorter window. This equality is everywhere in the sample. -/
theorem itoSimpleProcess_truncate (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ F) {t : ℝ≥0} (ht : t ≤ T) :
    itoSimpleProcess hBmeas (truncateSimple T hBmeas V).val t =
      itoSimpleProcess hBmeas V t := by
  classical
  have hsum : itoSimpleProcess hBmeas (truncateSimple T hBmeas V).val t =
      ∑ p ∈ V.value.support,
        itoSimpleProcess hBmeas (truncateCell T hBmeas V p).val t := by
    change ((simpleIntegralLM hBmeas t).comp
      (TBoundedSP (𝓖 := F) T hBmeas).subtype) (∑ p ∈ V.value.support, _) = _
    simp only [map_sum, LinearMap.comp_apply, Submodule.subtype_apply, simpleIntegralLM,
      LinearMap.coe_mk, AddHom.coe_mk]
  funext ω
  rw [hsum, Finset.sum_apply]
  conv_rhs => rw [itoSimpleProcess_apply, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hab := V.le_of_mem_support_value p hp
  by_cases haT : p.1 ≤ T
  · rw [truncateCell, dif_pos ⟨hab, haT⟩, itoSimpleProcess_stepSP]
    rw [min_assoc, min_eq_right ht]
  · have hTa : T ≤ p.1 := le_of_not_ge haT
    have hta : t ≤ p.1 := ht.trans hTa
    have htb : t ≤ p.2 := hta.trans hab
    rw [truncateCell, dif_neg (fun h => haT h.2)]
    simp [itoSimpleProcess_apply, min_eq_right hta, min_eq_right htb]

/-- The deterministic restriction also has the correct pointwise integrand,
away from time zero, which has zero time measure. -/
theorem truncateSimple_apply (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ F) {t : ℝ≥0} (htpos : 0 < t) (htT : t ≤ T) (ω : Ω) :
    (truncateSimple T hBmeas V).val t ω = V t ω := by
  classical
  have hsum : (truncateSimple T hBmeas V).val t ω =
      ∑ p ∈ V.value.support, (truncateCell T hBmeas V p).val t ω := by
    change ((simpleValueLM t ω).comp
      (TBoundedSP (𝓖 := F) T hBmeas).subtype) (∑ p ∈ V.value.support, _) = _
    simp only [map_sum, LinearMap.comp_apply, Submodule.subtype_apply, simpleValueLM,
      LinearMap.coe_mk, AddHom.coe_mk]
  rw [hsum]
  conv_rhs =>
    rw [SimpleProcess.apply_eq,
      Set.indicator_of_notMem (show t ∉ ({⊥} : Set ℝ≥0) from ne_of_gt htpos),
      zero_add, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hab := V.le_of_mem_support_value p hp
  by_cases haT : p.1 ≤ T
  · rw [truncateCell, dif_pos ⟨hab, haT⟩, SimpleProcess.apply_eq]
    simp [stepSP, Finsupp.sum_single_index, Set.indicator_apply, Set.mem_Ioc, htT]
  · rw [truncateCell, dif_neg (fun h => haT h.2)]
    have hnot : t ∉ Set.Ioc p.1 p.2 := fun h => haT (le_of_lt (h.1.trans_le htT))
    simp [hnot]

/-- Assembly commutes with restriction: the integrand on the shorter horizon
is the explicitly truncated simple process. -/
theorem restrictIntegrandCLM_simpleAssembly {T S : ℝ≥0} (hTS : T ≤ S)
    (hBmeas : ∀ t, Measurable (B t))
    (V : TBoundedSP (𝓖 := F) S hBmeas) :
    restrictIntegrandCLM hTS hBmeas (simpleAssembly_T (μ := μ) S hBmeas V) =
      simpleAssembly_T (μ := μ) T hBmeas (truncateSimple T hBmeas V.val) := by
  apply Lp.ext
  have hband : ∀ᵐ z ∂(trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas),
      z ∈ Set.Ioc 0 T ×ˢ (Set.univ : Set Ω) := by
    rw [← trimMeasure_restrict hTS hBmeas]
    exact ae_restrict_mem
      (measurableSet_predictable_Ioc_prod (𝓕 := F) 0 T MeasurableSet.univ)
  filter_upwards [restrictIntegrand_ae hTS hBmeas (simpleAssembly_T (μ := μ) S hBmeas V),
    ae_of_horizon_le hTS hBmeas (memLp_uncurry_trim_T S hBmeas V.val).coeFn_toLp,
    (memLp_uncurry_trim_T T hBmeas (truncateSimple T hBmeas V.val).val).coeFn_toLp,
    hband] with z hr hlarge hsmall hz
  change (restrictIntegrand hTS hBmeas (simpleAssembly_T (μ := μ) S hBmeas V) :
    ℝ≥0 × Ω → ℝ) z = _
  rw [hr, show (simpleAssembly_T (μ := μ) S hBmeas V : ℝ≥0 × Ω → ℝ) z =
      Function.uncurry ⇑V.val z from hlarge,
    show (simpleAssembly_T (μ := μ) T hBmeas (truncateSimple T hBmeas V.val) :
      ℝ≥0 × Ω → ℝ) z =
      Function.uncurry ⇑(truncateSimple T hBmeas V.val).val z from hsmall]
  exact (truncateSimple_apply T hBmeas V.val hz.1.1 hz.1.2 z.2).symm

/-- The elementary pointwise identity descends to equality in L². -/
theorem itoSimpleProcessLp_truncate (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ F) {t : ℝ≥0} (ht : t ≤ T) :
    itoSimpleProcessLp (μ := μ) hBmeas (truncateSimple T hBmeas V).val t =
      itoSimpleProcessLp (μ := μ) hBmeas V t := by
  apply Lp.ext
  filter_upwards [(memLp_itoSimpleProcess hBmeas
    (truncateSimple T hBmeas V).val t).coeFn_toLp,
    (memLp_itoSimpleProcess hBmeas V t).coeFn_toLp] with ω hs hl
  rw [show (itoSimpleProcessLp (μ := μ) hBmeas (truncateSimple T hBmeas V).val
    t : Ω → ℝ) ω = _ from hs,
    show (itoSimpleProcessLp (μ := μ) hBmeas V t : Ω → ℝ) ω = _ from hl]
  exact congrFun (itoSimpleProcess_truncate T hBmeas V ht) ω

/-- General predictable L² slice consistency is a conclusion of elementary
truncation and density, with no consistency premise. -/
theorem itoProcessCLM_restrict {T S : ℝ≥0} (hTS : T ≤ S)
    (hBmeas : ∀ t, Measurable (B t)) {t : ℝ≥0} (ht : t ≤ T)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) S hBmeas)) :
    itoProcessCLM (𝓖 := F) (μ := μ) T t hBmeas
        (restrictIntegrandCLM hTS hBmeas φ) =
      itoProcessCLM (𝓖 := F) (μ := μ) S t hBmeas φ := by
  refine (simpleAssembly_T_denseRange S hBmeas).induction_on φ ?_ ?_
  · exact isClosed_eq
      ((itoProcessCLM (𝓖 := F) (μ := μ) T t hBmeas).continuous.comp
        (restrictIntegrandCLM hTS hBmeas).continuous)
      (itoProcessCLM (𝓖 := F) (μ := μ) S t hBmeas).continuous
  · intro V
    rw [restrictIntegrandCLM_simpleAssembly hTS hBmeas V,
      itoProcessCLM_simpleAssembly_T, itoProcessCLM_simpleAssembly_T]
    exact itoSimpleProcessLp_truncate T hBmeas V.val ht

/-- Inclusion of the shorter compact time window. -/
def windowInclusion {T S : ℝ≥0} (hTS : T ≤ S) :
    C(Set.Icc (0 : ℝ≥0) T, Set.Icc (0 : ℝ≥0) S) :=
  ⟨fun t => ⟨t.val, t.property.1, t.property.2.trans hTS⟩,
    Continuous.subtype_mk continuous_subtype_val _⟩

/-- The installed continuous representative has the installed slice values. -/
theorem representative_eval_ae (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (t : Set.Icc (0 : ℝ≥0) T) :
    (fun ω => representative (continuousIto T hB hBmeas φ) ω t) =ᵐ[μ]
      (itoProcessCLM (𝓖 := F) (μ := μ) T t.val hBmeas φ : Ω → ℝ) := by
  have he := evalLp_ae t (continuousIto T hB hBmeas φ)
  rw [continuousIto_eval] at he
  filter_upwards [representative_indistinguishable (continuousIto T hB hBmeas φ), he]
    with ω h1 h2
  exact (h1 t).symm.trans h2.symm

/-- Cross-horizon consistency for every elementary integrand on the larger
horizon, using its explicitly constructed truncation on the shorter horizon. -/
theorem continuousIto_simple_overlap {T S : ℝ≥0} (hTS : T ≤ S)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (V : TBoundedSP (𝓖 := F) S hBmeas) :
    ∀ᵐ ω ∂μ, ∀ t : Set.Icc (0 : ℝ≥0) T,
      representative (continuousIto T hB hBmeas
        (simpleAssembly_T (μ := μ) T hBmeas (truncateSimple T hBmeas V.val))) ω t =
      representative (continuousIto S hB hBmeas
        (simpleAssembly_T (μ := μ) S hBmeas V)) ω (windowInclusion hTS t) := by
  letI : Nonempty (Set.Icc (0 : ℝ≥0) T) := ⟨⟨0, zero_le, zero_le⟩⟩
  apply ContinuousIntegralVersion.indistinguishable_of_dense_eq
    (TopologicalSpace.denseSeq _) (TopologicalSpace.denseRange_denseSeq _)
  · exact ae_of_all _ (fun ω => (representative _ ω).continuous)
  · exact ae_of_all _ (fun ω => (representative _ ω).continuous.comp
      (windowInclusion hTS).continuous)
  · intro n
    let t := TopologicalSpace.denseSeq (Set.Icc (0 : ℝ≥0) T) n
    have hsmall := representative_eval_ae T hB hBmeas
      (simpleAssembly_T (μ := μ) T hBmeas (truncateSimple T hBmeas V.val)) t
    have hlarge := representative_eval_ae S hB hBmeas
      (simpleAssembly_T (μ := μ) S hBmeas V) (windowInclusion hTS t)
    rw [itoProcessCLM_simpleAssembly_T] at hsmall hlarge
    have hLp : itoSimpleProcessLp (μ := μ) hBmeas (truncateSimple T hBmeas V.val).val t.val =
        itoSimpleProcessLp (μ := μ) hBmeas V.val t.val := by
      apply Lp.ext
      filter_upwards [(memLp_itoSimpleProcess hBmeas
        (truncateSimple T hBmeas V.val).val t.val).coeFn_toLp,
        (memLp_itoSimpleProcess hBmeas V.val t.val).coeFn_toLp] with ω hs hl
      rw [show (itoSimpleProcessLp (μ := μ) hBmeas (truncateSimple T hBmeas V.val).val
        t.val : Ω → ℝ) ω = _ from hs,
        show (itoSimpleProcessLp (μ := μ) hBmeas V.val t.val : Ω → ℝ) ω = _ from hl]
      exact congrFun (itoSimpleProcess_truncate T hBmeas V.val t.property.2) ω
    rw [hLp] at hsmall
    exact hsmall.trans hlarge.symm

/-- The installed continuous integrals on nested horizons are indistinguishable
on the overlap, for every integrand in the larger predictable L² space. -/
theorem continuousIto_overlap {T S : ℝ≥0} (hTS : T ≤ S)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) S hBmeas)) :
    ∀ᵐ ω ∂μ, ∀ t : Set.Icc (0 : ℝ≥0) T,
      representative (continuousIto T hB hBmeas
        (restrictIntegrandCLM hTS hBmeas φ)) ω t =
      representative (continuousIto S hB hBmeas φ) ω (windowInclusion hTS t) := by
  letI : Nonempty (Set.Icc (0 : ℝ≥0) T) := ⟨⟨0, zero_le, zero_le⟩⟩
  apply ContinuousIntegralVersion.indistinguishable_of_dense_eq
    (TopologicalSpace.denseSeq _) (TopologicalSpace.denseRange_denseSeq _)
  · exact ae_of_all _ (fun ω => (representative _ ω).continuous)
  · exact ae_of_all _ (fun ω => (representative _ ω).continuous.comp
      (windowInclusion hTS).continuous)
  · intro n
    let t := TopologicalSpace.denseSeq (Set.Icc (0 : ℝ≥0) T) n
    have hs := representative_eval_ae T hB hBmeas
      (restrictIntegrandCLM hTS hBmeas φ) t
    have hl := representative_eval_ae S hB hBmeas φ (windowInclusion hTS t)
    rw [itoProcessCLM_restrict hTS hBmeas t.property.2] at hs
    exact hs.trans hl.symm

/-- Countably many input-compatible predictable integrands have one common
exceptional set for all finite-window overlap identities. -/
theorem continuousIto_countable_overlap
    (L : ℕ → ℝ≥0) (hL : Monotone L)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (φ : ∀ n, Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) (L n) hBmeas))
    (hφ : ∀ (n m : ℕ) (hnm : n ≤ m),
      restrictIntegrandCLM (hL hnm) hBmeas (φ m) = φ n) :
    ∀ᵐ ω ∂μ, ∀ (n m : ℕ) (hnm : n ≤ m), ∀ t : Set.Icc (0 : ℝ≥0) (L n),
      representative (continuousIto (L n) hB hBmeas (φ n)) ω t =
      representative (continuousIto (L m) hB hBmeas (φ m)) ω
        (windowInclusion (hL hnm) t) := by
  apply ae_all_iff.mpr
  intro n
  apply ae_all_iff.mpr
  intro m
  by_cases hnm : n ≤ m
  · have h := continuousIto_overlap (hL hnm) hB hBmeas (φ m)
    rw [hφ n m hnm] at h
    exact h.mono fun ω hω _ => hω
  · exact ae_of_all _ fun _ h => (hnm h).elim

section HalfLine
variable (hB : ∀ ω, Continuous (fun t => B t ω))
  (hBmeas : ∀ t, Measurable (B t))
  (H : ℝ≥0 × Ω → ℝ)
  (hH : ∀ n : ℕ, MemLp H 2
    (trimMeasure_T (𝓖 := F) (μ := μ) (n : ℝ≥0) hBmeas))

/-- The integer-window integrands are the L² classes of a single raw integrand. -/
def integerIntegrand (n : ℕ) :
    Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) (n : ℝ≥0) hBmeas) :=
  (hH n).toLp H

/-- Input compatibility is proved from the common representative H. -/
theorem integerIntegrand_restrict (n m : ℕ) (hnm : n ≤ m) :
    restrictIntegrandCLM (show (n : ℝ≥0) ≤ m by exact_mod_cast hnm) hBmeas
      (integerIntegrand hBmeas H hH m) = integerIntegrand hBmeas H hH n := by
  apply Lp.ext
  have hnm' : (n : ℝ≥0) ≤ m := by exact_mod_cast hnm
  filter_upwards [restrictIntegrand_ae hnm' hBmeas (integerIntegrand hBmeas H hH m),
    ae_of_horizon_le hnm' hBmeas (hH m).coeFn_toLp,
    (hH n).coeFn_toLp] with z hr hm hn
  change (restrictIntegrand hnm' hBmeas (integerIntegrand hBmeas H hH m) :
    ℝ≥0 × Ω → ℝ) z = _
  rw [hr, show (integerIntegrand hBmeas H hH m : ℝ≥0 × Ω → ℝ) z = H z from hm,
    show (integerIntegrand hBmeas H hH n : ℝ≥0 × Ω → ℝ) z = H z from hn]

/-- The path integral on one integer window. -/
def integerItoPath (n : ℕ) (ω : Ω) : C(Set.Icc (0 : ℝ≥0) (n : ℝ≥0), ℝ) :=
  representative (continuousIto (n : ℝ≥0) hB hBmeas
    (integerIntegrand hBmeas H hH n)) ω

/-- One common event for every integer-window overlap, produced from H. -/
theorem integerItoPath_overlap :
    ∀ᵐ ω ∂μ, ∀ (n m : ℕ) (hnm : n ≤ m), ∀ t : Set.Icc (0 : ℝ≥0) (n : ℝ≥0),
      integerItoPath hB hBmeas H hH n ω t =
      integerItoPath hB hBmeas H hH m ω
        (windowInclusion (show (n : ℝ≥0) ≤ m by exact_mod_cast hnm) t) := by
  exact continuousIto_countable_overlap (fun n => (n : ℝ≥0))
    Nat.mono_cast hB hBmeas
    (integerIntegrand hBmeas H hH)
    (integerIntegrand_restrict hBmeas H hH)

/-- A deterministic integer horizon lying strictly beyond the evaluation time. -/
def coveringHorizon (t : ℝ≥0) : ℕ := Nat.ceil (t : ℝ) + 1

theorem lt_coveringHorizon (t : ℝ≥0) : t < (coveringHorizon t : ℝ≥0) := by
  change (t : ℝ) < ((Nat.ceil (t : ℝ) + 1 : ℕ) : ℝ)
  have h := Nat.le_ceil (t : ℝ)
  exact lt_of_le_of_lt h (by push_cast; exact lt_add_one _)

/-- The half-line process is selected from the installed integer-window paths. -/
def halfLineIto (t : ℝ≥0) (ω : Ω) : ℝ :=
  integerItoPath hB hBmeas H hH (coveringHorizon t) ω
    ⟨t, zero_le, (lt_coveringHorizon t).le⟩

/-- On the common overlap event, the selection agrees with every covering
integer window. This is a deterministic implication used in the patch proof. -/
theorem halfLineIto_eq_integer_on_event (ω : Ω)
    (hω : ∀ (n m : ℕ) (hnm : n ≤ m), ∀ t : Set.Icc (0 : ℝ≥0) (n : ℝ≥0),
      integerItoPath hB hBmeas H hH n ω t =
      integerItoPath hB hBmeas H hH m ω
        (windowInclusion (show (n : ℝ≥0) ≤ m by exact_mod_cast hnm) t))
    (n : ℕ) (t : ℝ≥0) (ht : t ≤ (n : ℝ≥0)) :
    halfLineIto hB hBmeas H hH t ω =
      integerItoPath hB hBmeas H hH n ω ⟨t, zero_le, ht⟩ := by
  rcases le_total (coveringHorizon t) n with h | h
  · exact hω (coveringHorizon t) n h ⟨t, zero_le, (lt_coveringHorizon t).le⟩
  · exact (hω n (coveringHorizon t) h ⟨t, zero_le, ht⟩).symm

/-- Every slice is measurable: the selected horizon depends only on time. -/
theorem halfLineIto_stronglyMeasurable (t : ℝ≥0) :
    StronglyMeasurable (halfLineIto hB hBmeas H hH t) := by
  exact (ContinuousMap.evalCLM ℝ
    (⟨t, zero_le, (lt_coveringHorizon t).le⟩ :
      Set.Icc (0 : ℝ≥0) (coveringHorizon t : ℝ≥0))).continuous.comp_stronglyMeasurable
      (representative_stronglyMeasurable _)

/-- Clamping embeds the entire half-line continuously into a compact window. -/
def clampToWindow (n : ℕ) : C(ℝ≥0, Set.Icc (0 : ℝ≥0) (n : ℝ≥0)) :=
  ⟨fun t => ⟨min t n, zero_le, min_le_right _ _⟩,
    Continuous.subtype_mk (continuous_id.min continuous_const) _⟩

/-- The process selected from integer windows has continuous paths outside
one null set. No output consistency assumption occurs in the statement. -/
theorem halfLineIto_ae_continuous :
    ∀ᵐ ω ∂μ, Continuous (fun t => halfLineIto hB hBmeas H hH t ω) := by
  filter_upwards [integerItoPath_overlap hB hBmeas H hH] with ω hω
  apply continuous_iff_continuousAt.mpr
  intro t
  let n := coveringHorizon t
  have htn : t < (n : ℝ≥0) := lt_coveringHorizon t
  have hc : Continuous (fun s : ℝ≥0 =>
      integerItoPath hB hBmeas H hH n ω (clampToWindow n s)) :=
    (integerItoPath hB hBmeas H hH n ω).continuous.comp (clampToWindow n).continuous
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds htn] with s hs
  have he := halfLineIto_eq_integer_on_event hB hBmeas H hH ω hω n s hs.le
  first
  | simpa only [clampToWindow, ContinuousMap.coe_mk, min_eq_left hs.le] using he
  | simpa only [clampToWindow, ContinuousMap.coe_mk, min_eq_left hs.le] using he.symm

/-- The half-line process agrees simultaneously with every installed integer
window, including each endpoint. -/
theorem halfLineIto_integer_agreement :
    ∀ᵐ ω ∂μ, ∀ n : ℕ, ∀ t : Set.Icc (0 : ℝ≥0) (n : ℝ≥0),
      halfLineIto hB hBmeas H hH t.val ω = integerItoPath hB hBmeas H hH n ω t := by
  filter_upwards [integerItoPath_overlap hB hBmeas H hH] with ω hω n t
  exact halfLineIto_eq_integer_on_event hB hBmeas H hH ω hω n t.val t.property.2

/-- The raw integrand's class on an arbitrary finite horizon, obtained by
restriction from an integer window lying beyond it. -/
def finiteIntegrand (T : ℝ≥0) :
    Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) :=
  restrictIntegrandCLM (lt_coveringHorizon T).le hBmeas
    (integerIntegrand hBmeas H hH (coveringHorizon T))

/-- The finite-horizon constructor represents the same raw integrand H. -/
theorem finiteIntegrand_ae (T : ℝ≥0) :
    (finiteIntegrand hBmeas H hH T : ℝ≥0 × Ω → ℝ) =ᵐ[
      trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas] H :=
  (restrictIntegrand_ae (lt_coveringHorizon T).le hBmeas
    (integerIntegrand hBmeas H hH (coveringHorizon T))).trans
    (ae_of_horizon_le (lt_coveringHorizon T).le hBmeas
      (hH (coveringHorizon T)).coeFn_toLp)

/-- On every finite horizon the half-line process is indistinguishable from
the installed continuous Itô integral of the raw integrand H. -/
theorem halfLineIto_finite_agreement (T : ℝ≥0) :
    ∀ᵐ ω ∂μ, ∀ t : Set.Icc (0 : ℝ≥0) T,
      halfLineIto hB hBmeas H hH t.val ω =
      representative (continuousIto T hB hBmeas
        (finiteIntegrand hBmeas H hH T)) ω t := by
  have hover := continuousIto_overlap (lt_coveringHorizon T).le hB hBmeas
    (integerIntegrand hBmeas H hH (coveringHorizon T))
  filter_upwards [halfLineIto_integer_agreement hB hBmeas H hH, hover] with ω hi ho t
  exact (hi (coveringHorizon T) (windowInclusion (lt_coveringHorizon T).le t)).trans
    (ho t).symm

/-- The half-line process has exactly the installed L² slice integral values
at every fixed time in every finite window. -/
theorem halfLineIto_modification (T : ℝ≥0) (t : Set.Icc (0 : ℝ≥0) T) :
    halfLineIto hB hBmeas H hH t.val =ᵐ[μ]
      (itoProcessCLM (𝓖 := F) (μ := μ) T t.val hBmeas
        (finiteIntegrand hBmeas H hH T) : Ω → ℝ) :=
  by
  filter_upwards [halfLineIto_finite_agreement hB hBmeas H hH T,
    representative_eval_ae T hB hBmeas (finiteIntegrand hBmeas H hH T) t] with ω h1 h2
  exact (h1 t).trans h2

end HalfLine

end Ripple.Stochastic.ContinuousItoConsistency
