import Ripple.Stochastic.StrongSDEConcreteMaps

/-!
# Embedding solutions in the adapted path space

Bounded coefficients produce the compact path moment from
the equation itself. In particular, the moment is not an input of
`solution_memLp`. The last theorem constructs an everywhere continuous adapted
modification of any adapted process with almost surely continuous paths.
Transferring an integral equation through that modification additionally uses
the predictable-integral congruence theorem.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace Ripple.Stochastic.StrongSDESolutionSpace
open AdaptedContinuousSpace StrongSDEConcreteMaps
open ContinuousAdaptedIntegrand ContinuousItoElementary

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The measurable-evaluation argument also applies to vector paths. -/
theorem vector_stronglyMeasurable_of_evaluations
    {L : Type*} [MetricSpace L] [CompactSpace L]
    [SecondCountableTopology L] [Nonempty L]
    (f : Ω → C(L, E)) (hf : ∀ t, Measurable (fun ω => f ω t)) :
    StronglyMeasurable f := by
  letI : MeasurableSpace C(L, E) := borel C(L, E)
  let d : ℕ → L := TopologicalSpace.denseSeq L
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq L
  let e : C(L, E) → ℕ → E := fun g n => g (d n)
  have hecont : Continuous e :=
    continuous_pi fun n => (ContinuousMap.evalCLM ℝ (d n)).continuous
  have heinj : Function.Injective e := by
    intro f g hfg
    apply ContinuousMap.coe_injective
    exact hd.equalizer f.continuous g.continuous hfg
  have he : MeasurableEmbedding e := hecont.measurableEmbedding heinj
  have hcomp : Measurable (e ∘ f) := measurable_pi_iff.mpr fun n => hf (d n)
  exact (he.measurable_comp_iff.mp hcomp).stronglyMeasurable

def samplePath (T : ℝ≥0) (Z : ℝ≥0 → Ω → E)
    (hc : ∀ ω, Continuous (fun t => Z t ω)) (ω : Ω) : C(Window T, E) :=
  ⟨fun t => Z t.val ω, (hc ω).comp continuous_subtype_val⟩

theorem samplePath_stronglyMeasurable (F : Filtration ℝ≥0 mΩ)
    (T : ℝ≥0) (Z : ℝ≥0 → Ω → E) (ha : StronglyAdapted F Z)
    (hc : ∀ ω, Continuous (fun t => Z t ω)) :
    StronglyMeasurable (samplePath T Z hc) := by
  apply vector_stronglyMeasurable_of_evaluations
  exact fun t => ((ha t.val).mono (F.le t.val)).measurable

theorem samplePath_drift (T : ℝ≥0) (Z : ℝ≥0 → Ω → E)
    (hc : ∀ ω, Continuous (fun t => Z t ω))
    (b : E → E) (hb : Continuous b) (ω : Ω) (t : Window T) :
    driftPath T b hb (samplePath T Z hc ω) t =
      ∫ s in (0 : ℝ)..(t.val : ℝ), b (Z s.toNNReal ω) := by
  change (∫ s in (0 : ℝ)..(t.val : ℝ),
    b (Z (min s.toNNReal T) ω)) = _
  rw [intervalIntegral.integral_of_le t.val.coe_nonneg,
    intervalIntegral.integral_of_le t.val.coe_nonneg]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  have hst : s.toNNReal ≤ T :=
    (Real.toNNReal_le_iff_le_coe.mpr hs.2).trans t.property.2
  show b (Z (min s.toNNReal T) ω) = b (Z s.toNNReal ω)
  rw [min_eq_left hst]

private theorem memLp_sum_paths {T : ℝ≥0} {ι : Type*} (s : Finset ι)
    (f : ι → Ω → C(Window T, E)) (hf : ∀ i ∈ s, MemLp (f i) 2 μ) :
    MemLp (fun ω => ∑ i ∈ s, f i ω) 2 μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact memLp_const _
  | @insert i s hi ih =>
    have h := (hf i (Finset.mem_insert_self _ _)).sub
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))).neg
    refine h.ae_eq (ae_of_all _ fun ω => ?_)
    show f i ω - -(∑ j ∈ s, f j ω) = ∑ j ∈ insert i s, f j ω
    rw [sub_neg_eq_add, Finset.sum_insert hi]

/-- A scalar integral embedded in a direction has an actual path L² moment. -/
theorem directionRepresentative_memLp (T : ℝ≥0) (v : E)
    (J : PathLp (Window T) μ) :
    MemLp (fun ω => directionPathCLM v (representative J ω)) 2 μ := by
  apply (Lp.memLp (directionPathLp v J)).ae_eq
  filter_upwards [directionPathLp_ae v J, representative_ae J] with ω hj hr
  rw [hj, hr]

/-- A solution with continuous adapted paths has a finite second path moment
because every term on its right-hand side does. No moment of Z is assumed.
The integral is the actual `windowIto`, and its input membership is proved. -/
theorem solution_memLp {ι : Type*} [Fintype ι]
    (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (B : ι → ℝ≥0 → Ω → ℝ) [∀ i, IsFilteredPreBrownian (B i) F μ]
    (hB : ∀ i ω, Continuous (fun t => B i t ω))
    (hBmeas : ∀ i t, Measurable (B i t))
    (ell : ι → E) (g : ι → E → ℝ) (hg : ∀ i, Continuous (g i))
    (K : ι → ℝ) (hK : ∀ i x, |g i x| ≤ K i)
    (b : E → E) {Lb : ℝ≥0} (hb : LipschitzWith Lb b)
    (C : ℝ) (hC : 0 ≤ C) (hbC : ∀ x, ‖b x‖ ≤ C)
    (x₀ : E) (N : ℕ) (Z : ℝ≥0 → Ω → E)
    (ha : StronglyAdapted F Z) (hc : ∀ ω, Continuous (fun t => Z t ω))
    (hEq : ∀ᵐ ω ∂μ, ∀ t ≤ T, Z t ω =
      StrongSDE.sdeRhs (fun i => windowIto (μ := μ) F T (B i) (hB i) (hBmeas i))
        ell g b x₀ N Z t ω) :
    MemLp (samplePath T Z hc) 2 μ := by
  classical
  let H : ι → ℝ≥0 → Ω → ℝ := fun i t ω => g i (Z t ω)
  have hm : ∀ i, MemLp (Function.uncurry (H i)) 2
      (FilteredItoIntegralCLM.trimMeasure_T (𝓖 := F) (μ := μ) T (hBmeas i)) := by
    intro i
    exact integrandMemLp (μ := μ) T (hBmeas i) (H i)
      (measurable_comp_sections (fun t => (ha t).measurable) (hg i))
      (continuous_comp_paths hc (hg i)) (K i) (fun _ _ => hK i _)
  let J : ι → PathLp (Window T) μ := fun i =>
    continuousIto T (hB i) (hBmeas i) ((hm i).toLp (Function.uncurry (H i)))
  let Q : ι → Ω → C(Window T, E) := fun i ω =>
    directionPathCLM ((Real.sqrt (N : ℝ))⁻¹ • ell i) (representative (J i) ω)
  have hQ : ∀ i, MemLp (Q i) 2 μ := fun i => directionRepresentative_memLp T _ _
  let D : Ω → C(Window T, E) := fun ω =>
    driftPath T b hb.continuous (samplePath T Z hc ω)
  have hD : MemLp D 2 μ := by
    apply MemLp.of_bound
      ((driftPath_lipschitz T b hb).continuous.comp_stronglyMeasurable
        (samplePath_stronglyMeasurable F T Z ha hc)).aestronglyMeasurable ((T : ℝ) * C)
    exact ae_of_all _ fun ω => driftPath_norm_le T b hb.continuous C hC hbC _
  let R : Ω → C(Window T, E) := fun ω =>
    ContinuousMap.const (Window T) x₀ + (∑ i, Q i ω) + D ω
  have hR : MemLp R 2 μ := by
    have h := ((memLp_const (μ := μ) (p := 2) (ContinuousMap.const (Window T) x₀)).sub
      (memLp_sum_paths Finset.univ Q (fun i _ => hQ i)).neg).sub hD.neg
    refine h.ae_eq (ae_of_all _ fun ω => ?_)
    show ContinuousMap.const (Window T) x₀ - -(∑ i ∈ Finset.univ, Q i ω) - -D ω = R ω
    simp only [sub_neg_eq_add, R]
  apply hR.ae_eq
  filter_upwards [hEq] with ω hω
  apply ContinuousMap.ext
  intro t
  change x₀ + (∑ i, Q i ω) t + D ω t = Z t.val ω
  rw [hω t.val t.property.2]
  change x₀ + (∑ i, Q i ω) t +
    driftPath T b hb.continuous (samplePath T Z hc ω) t = _
  rw [samplePath_drift]
  unfold StrongSDE.sdeRhs
  congr 2
  simp only [ContinuousMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hcap : cappedTime T t.val = t := Subtype.ext (min_eq_left t.property.2)
  simp only [Q, directionPathCLM, LinearMap.mkContinuous_apply,
    windowIto, dif_pos (hm i), hcap, J, H, smul_smul]
  rw [mul_comm]
  rfl

/-- The square supremum is integrable for every continuous adapted solution. -/
theorem solution_supMoment (T : ℝ≥0) (Z : ℝ≥0 → Ω → E)
    (hc : ∀ ω, Continuous (fun t => Z t ω))
    (hm : MemLp (samplePath T Z hc) 2 μ) :
    Integrable (fun ω => ⨆ t : Window T, ‖Z t.val ω‖ ^ 2) μ := by
  have h := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have heq : (fun ω => ⨆ t : Window T, ‖Z t.val ω‖ ^ 2) =
      fun ω => ‖samplePath T Z hc ω‖ ^ 2 := by
    funext ω
    exact vectorPath_sup_sq (samplePath T Z hc ω)
  rwa [heq]

/-- Embedding is constructed from the original path, and is faithful at all
window times on one event. A separate null set for each time is not used. -/
def ofProcess (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (Z : ℝ≥0 → Ω → E) (ha : StronglyAdapted F Z)
    (hc : ∀ ω, Continuous (fun t => Z t ω))
    (hm : MemLp (samplePath T Z hc) 2 μ) : State (E := E) (μ := μ) F T := by
  refine ⟨hm.toLp _, (mem_vectorAdaptedSubmodule _ _).mpr ?_⟩
  intro t
  apply mem_lpMeas_iff_aestronglyMeasurable.mpr
  apply (ha t.val).aestronglyMeasurable.congr
  filter_upwards [vectorEvalLp_ae t (hm.toLp _), hm.coeFn_toLp] with ω he hp
  rw [he, hp]
  rfl

theorem ofProcess_realize (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (Z : ℝ≥0 → Ω → E) (ha : StronglyAdapted F Z)
    (hc : ∀ ω, Continuous (fun t => Z t ω))
    (hm : MemLp (samplePath T Z hc) 2 μ) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T, realize F T (ofProcess F T Z ha hc hm) t ω = Z t ω := by
  filter_upwards [vectorRepresentative_ae (ofProcess F T Z ha hc hm).val,
    hm.coeFn_toLp] with ω hr hp
  have hval : (ofProcess F T Z ha hc hm).val = hm.toLp _ := rfl
  intro t ht
  change vectorRepresentative _ ω (cappedTime T t) = _
  rw [← hr, hval, hp]
  change Z (min t T) ω = _
  rw [min_eq_left ht]

/-- Augmentation permits resetting one ambient measurable null set. This
turns a.s. path continuity into everywhere path continuity without losing
adaptation or changing any time on the common full-measure event. -/
theorem exists_continuous_adapted_modification
    (F : Filtration ℝ≥0 mΩ)
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (Z : ℝ≥0 → Ω → E) (ha : StronglyAdapted F Z)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => Z t ω)) :
    ∃ Y : ℝ≥0 → Ω → E, StronglyAdapted F Y ∧
      (∀ ω, Continuous (fun t => Y t ω)) ∧
      (∀ᵐ ω ∂μ, ∀ t, Y t ω = Z t ω) := by
  classical
  obtain ⟨A, hsub, hAm, hAz⟩ :=
    exists_measurable_superset_of_null (μ := μ) (ae_iff.mp hc)
  let Y : ℝ≥0 → Ω → E := fun t ω => if ω ∈ A then 0 else Z t ω
  have hAae : ∀ᵐ ω ∂μ, ω ∉ A := by
    rw [ae_iff]
    simpa only [not_not] using hAz
  refine ⟨Y, ?_, ?_, ?_⟩
  · intro t
    exact (Measurable.ite (hnull t A hAm hAz) measurable_const
      (ha t).measurable).stronglyMeasurable
  · intro ω
    by_cases hω : ω ∈ A
    · simpa only [Y, if_pos hω] using (continuous_const : Continuous (fun _ : ℝ≥0 => (0 : E)))
    · have hcont : Continuous (fun t => Z t ω) := by
        by_contra hbad
        exact hω (hsub hbad)
      simpa only [Y, if_neg hω] using hcont
  · filter_upwards [hAae] with ω hω
    exact fun t => if_neg hω

/-- One sample-null set remains null for the predictable product measure.
This uses a predictable rectangle containing every exceptional pair; it does
not presume joint measurability of the original exceptional process. -/
theorem uncurry_ae_eq_of_indistinguishable {V : Type*}
    (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (B : ℝ≥0 → Ω → ℝ) (hBmeas : ∀ t, Measurable (B t))
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (H G : ℝ≥0 → Ω → V)
    (h : ∀ᵐ ω ∂μ, ∀ t ≤ T, H t ω = G t ω) :
    Function.uncurry H =ᵐ[FilteredItoIntegralCLM.trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas]
      Function.uncurry G := by
  obtain ⟨A, hsub, hAm, hAz⟩ :=
    exists_measurable_superset_of_null (μ := μ) (ae_iff.mp h)
  let S : Set (ℝ≥0 × Ω) := Ioc 0 T ×ˢ A
  have hS : MeasurableSet[F.predictable] S :=
    measurableSet_predictable_Ioc_prod (𝓕 := F) 0 T (hnull 0 A hAm hAz)
  have hSz : FilteredItoIntegralCLM.trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas S = 0 := by
    change (((FilteredItoIntegralCLM.timeMeasure_T T).prod μ).trim F.predictable_le_prod) S = 0
    rw [trim_measurableSet_eq F.predictable_le_prod hS]
    change ((FilteredItoIntegralCLM.timeMeasure_T T).prod μ) (Ioc 0 T ×ˢ A) = 0
    rw [Measure.prod_prod, hAz, mul_zero]
  have hSae : ∀ᵐ z ∂(FilteredItoIntegralCLM.trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas),
      z ∉ S := by
    rw [ae_iff]
    simpa only [not_not] using hSz
  have hwin : ∀ᵐ z ∂(FilteredItoIntegralCLM.trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas),
      z.1 ∈ Ioc 0 T := by
    rw [FilteredItoIntegralCLM.trimMeasure_T_eq_restrict]
    have hset : MeasurableSet[F.predictable] (Ioc 0 T ×ˢ (univ : Set Ω)) :=
      measurableSet_predictable_Ioc_prod (𝓕 := F) 0 T MeasurableSet.univ
    filter_upwards [ae_restrict_mem hset] with z hz
    exact hz.1
  filter_upwards [hSae, hwin] with z hz ht
  have hzA : z.2 ∉ A := fun hA => hz ⟨ht, hA⟩
  have hgood : ∀ t ≤ T, H t z.2 = G t z.2 := by
    by_contra hbad
    exact hzA (hsub hbad)
  exact hgood z.1 ht.2

/-- Equal predictable input classes give literally the same selected integral
representative. The domain test in `windowIto` is invariant under a.e. equality. -/
theorem windowIto_congr (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (B : ℝ≥0 → Ω → ℝ) [IsFilteredPreBrownian B F μ]
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (H G : ℝ≥0 → Ω → ℝ)
    (h : Function.uncurry H =ᵐ[FilteredItoIntegralCLM.trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas]
      Function.uncurry G) :
    windowIto (μ := μ) F T B hB hBmeas H = windowIto (μ := μ) F T B hB hBmeas G := by
  classical
  by_cases hm : MemLp (Function.uncurry H) 2
      (FilteredItoIntegralCLM.trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)
  · have hn := hm.ae_eq h
    have heq : hm.toLp (Function.uncurry H) = hn.toLp (Function.uncurry G) := by
      apply Lp.ext
      exact hm.coeFn_toLp.trans (h.trans hn.coeFn_toLp.symm)
    funext t ω
    simp only [windowIto, dif_pos hm, dif_pos hn, heq]
  · have hn : ¬MemLp (Function.uncurry G) 2
        (FilteredItoIntegralCLM.trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) :=
      fun hG => hm (hG.ae_eq h.symm)
    funext t ω
    simp only [windowIto, dif_neg hm, dif_neg hn]

/-- Bounded continuous coefficients of an adapted a.s. continuous process
belong to the installed predictable domain before any moment is known. -/
theorem coefficient_memLp_of_ae_continuous
    (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (B : ℝ≥0 → Ω → ℝ) (hBmeas : ∀ t, Measurable (B t))
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (Z : ℝ≥0 → Ω → E) (ha : StronglyAdapted F Z)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => Z t ω))
    (g : E → ℝ) (hg : Continuous g) (K : ℝ) (hK : ∀ x, |g x| ≤ K) :
    MemLp (Function.uncurry (fun t ω => g (Z t ω))) 2
      (FilteredItoIntegralCLM.trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) := by
  obtain ⟨Y, hYa, hYc, hYZ⟩ := exists_continuous_adapted_modification F hnull Z ha hc
  have hm := integrandMemLp (μ := μ) T hBmeas (fun t ω => g (Y t ω))
    (measurable_comp_sections (fun t => (hYa t).measurable) hg)
    (continuous_comp_paths hYc hg) K (fun _ _ => hK _)
  apply hm.ae_eq
  apply uncurry_ae_eq_of_indistinguishable F T B hBmeas hnull
  filter_upwards [hYZ] with ω hω
  exact fun t _ => congrArg g (hω t)

/-- The actual equation respects indistinguishability on its entire window.
Only equality on the window is needed, even though processes are all-time functions. -/
theorem sdeRhs_congr {ι : Type*} [Fintype ι]
    (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (B : ι → ℝ≥0 → Ω → ℝ) [∀ i, IsFilteredPreBrownian (B i) F μ]
    (hB : ∀ i ω, Continuous (fun t => B i t ω))
    (hBmeas : ∀ i t, Measurable (B i t))
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (ell : ι → E) (g : ι → E → ℝ) (b : E → E) (x₀ : E) (N : ℕ)
    (X Y : ℝ≥0 → Ω → E)
    (h : ∀ᵐ ω ∂μ, ∀ t ≤ T, X t ω = Y t ω) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T,
      StrongSDE.sdeRhs (fun i => windowIto (μ := μ) F T (B i) (hB i) (hBmeas i)) ell g b x₀ N X t ω =
      StrongSDE.sdeRhs (fun i => windowIto (μ := μ) F T (B i) (hB i) (hBmeas i)) ell g b x₀ N Y t ω := by
  have hi : ∀ i, windowIto (μ := μ) F T (B i) (hB i) (hBmeas i) (fun s ω => g i (X s ω)) =
      windowIto (μ := μ) F T (B i) (hB i) (hBmeas i) (fun s ω => g i (Y s ω)) := by
    intro i
    apply windowIto_congr
    apply uncurry_ae_eq_of_indistinguishable F T (B i) (hBmeas i) hnull
    filter_upwards [h] with ω hω
    exact fun t ht => congrArg (g i) (hω t ht)
  filter_upwards [h] with ω hω
  intro t ht
  unfold StrongSDE.sdeRhs
  simp only [hi]
  congr 1
  rw [intervalIntegral.integral_of_le t.coe_nonneg,
    intervalIntegral.integral_of_le t.coe_nonneg]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  simp only [hω s.toNNReal ((Real.toNNReal_le_iff_le_coe.mpr hs.2).trans ht)]

/-- Bounded coefficients imply a finite compact-window second supremum moment
for every adapted a.s. continuous solution of the actual equation. No moment,
predictable membership or everywhere-continuity premise is imposed on Z. -/
theorem arbitrary_solution_supMoment {ι : Type*} [Fintype ι]
    (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (B : ι → ℝ≥0 → Ω → ℝ) [∀ i, IsFilteredPreBrownian (B i) F μ]
    (hB : ∀ i ω, Continuous (fun t => B i t ω))
    (hBmeas : ∀ i t, Measurable (B i t))
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (ell : ι → E) (g : ι → E → ℝ) (hg : ∀ i, Continuous (g i))
    (K : ι → ℝ) (hK : ∀ i x, |g i x| ≤ K i)
    (b : E → E) {Lb : ℝ≥0} (hb : LipschitzWith Lb b)
    (C : ℝ) (hC : 0 ≤ C) (hbC : ∀ x, ‖b x‖ ≤ C)
    (x₀ : E) (N : ℕ) (Z : ℝ≥0 → Ω → E)
    (ha : StronglyAdapted F Z) (hc : ∀ᵐ ω ∂μ, Continuous (fun t => Z t ω))
    (hEq : ∀ᵐ ω ∂μ, ∀ t ≤ T, Z t ω =
      StrongSDE.sdeRhs (fun i => windowIto (μ := μ) F T (B i) (hB i) (hBmeas i))
        ell g b x₀ N Z t ω) :
    Integrable (fun ω => ⨆ t : Window T, ‖Z t.val ω‖ ^ 2) μ := by
  obtain ⟨Y, hYa, hYc, hYZ⟩ := exists_continuous_adapted_modification F hnull Z ha hc
  have hwindow : ∀ᵐ ω ∂μ, ∀ t ≤ T, Y t ω = Z t ω :=
    hYZ.mono fun _ h t _ => h t
  have hrhs := sdeRhs_congr F T B hB hBmeas hnull ell g b x₀ N Y Z hwindow
  have hYEq : ∀ᵐ ω ∂μ, ∀ t ≤ T, Y t ω =
      StrongSDE.sdeRhs (fun i => windowIto (μ := μ) F T (B i) (hB i) (hBmeas i))
        ell g b x₀ N Y t ω := by
    filter_upwards [hwindow, hEq, hrhs] with ω hy hz hr
    exact fun t ht => (hy t ht).trans ((hz t ht).trans (hr t ht).symm)
  have hm := solution_memLp F T B hB hBmeas ell g hg K hK b hb C hC hbC
    x₀ N Y hYa hYc hYEq
  apply (solution_supMoment T Y hYc hm).congr
  filter_upwards [hYZ] with ω hω
  congr 1
  funext t
  rw [hω t.val]

end Ripple.Stochastic.StrongSDESolutionSpace
