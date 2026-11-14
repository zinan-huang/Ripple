import Ripple.Stochastic.StrongSDEConcreteMaps
import Ripple.Stochastic.StrongSDEPicardIterates
import Ripple.Stochastic.StoppedContinuousIto
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.CompactOpen

/-!
# The actual running squared distance on the continuous adapted carrier

Stopping acts on continuous vector paths and
then on their Bochner L² classes. Dominated convergence proves continuity of
the expected squared running norm. These constructions use the same carrier
and representatives as the concrete Picard map.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace Ripple.Stochastic.StrongSDERunningMoment
open StrongSDEConcreteMaps AdaptedContinuousSpace
open StoppedContinuousIto FilteredItoIntegralL2 FilteredItoIntegralCLM

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Deterministic stopping of a vector-valued continuous path. -/
def vectorStopPath (T t : ℝ≥0) :
    C(StrongSDEConcreteMaps.Window T, E) →L[ℝ] C(StrongSDEConcreteMaps.Window T, E) :=
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

@[simp] theorem vectorStopPath_apply (T t : ℝ≥0)
    (x : C(StrongSDEConcreteMaps.Window T, E)) (s : StrongSDEConcreteMaps.Window T) :
    vectorStopPath T t x s = x (stopTime T t s) := rfl

theorem vectorStopPath_norm_le (T t : ℝ≥0)
    (x : C(StrongSDEConcreteMaps.Window T, E)) : ‖vectorStopPath T t x‖ ≤ ‖x‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg x)).mpr
  intro s
  exact x.norm_coe_le_norm _

theorem vectorStopPath_eval_le (T t : ℝ≥0)
    (x : C(StrongSDEConcreteMaps.Window T, E))
    (s : StrongSDEConcreteMaps.Window T) (hs : s.val ≤ t) :
    ‖x s‖ ≤ ‖vectorStopPath T t x‖ := by
  have hstop : stopTime T t s = s := Subtype.ext (min_eq_left hs)
  simpa only [vectorStopPath_apply, hstop] using
    (vectorStopPath T t x).norm_coe_le_norm s

theorem vectorStopPath_terminal (T : ℝ≥0)
    (x : C(StrongSDEConcreteMaps.Window T, E)) : vectorStopPath T T x = x := by
  ext s
  have hs : stopTime T T s = s := Subtype.ext (min_eq_left s.property.2)
  simp only [vectorStopPath_apply, hs]

/-- Restriction of a continuous path to a smaller initial time window. -/
def prefixPath {t T : ℝ≥0} (ht : t ≤ T)
    (x : C(StrongSDEConcreteMaps.Window T, E)) :
    C(StrongSDEConcreteMaps.Window t, E) :=
  ⟨fun s => x ⟨s.val, s.property.1, s.property.2.trans ht⟩,
    x.continuous.comp (continuous_subtype_val.subtype_mk _)⟩

@[simp] theorem prefixPath_apply {t T : ℝ≥0} (ht : t ≤ T)
    (x : C(StrongSDEConcreteMaps.Window T, E))
    (s : StrongSDEConcreteMaps.Window t) :
    prefixPath ht x s = x ⟨s.val, s.property.1, s.property.2.trans ht⟩ := rfl

/-- Stopping on the larger window and restricting to the smaller window have
the same uniform norm: stopping repeats values already attained in the prefix. -/
theorem vectorStopPath_norm_eq_prefixPath_norm {t T : ℝ≥0} (ht : t ≤ T)
    (x : C(StrongSDEConcreteMaps.Window T, E)) :
    ‖vectorStopPath T t x‖ = ‖prefixPath ht x‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg (prefixPath ht x))).mpr
    intro s
    let r : StrongSDEConcreteMaps.Window t :=
      ⟨min s.val t, zero_le, min_le_right _ _⟩
    have heq : (⟨r.val, r.property.1, r.property.2.trans ht⟩ :
        StrongSDEConcreteMaps.Window T) = stopTime T t s := Subtype.ext rfl
    simpa only [prefixPath_apply, heq, vectorStopPath_apply] using
      (prefixPath ht x).norm_coe_le_norm r
  · apply (ContinuousMap.norm_le _ (norm_nonneg (vectorStopPath T t x))).mpr
    intro s
    exact vectorStopPath_eval_le T t x
      ⟨s.val, s.property.1, s.property.2.trans ht⟩ s.property.2

/-- For each fixed continuous path, deterministic stopping varies continuously
in the uniform norm. Compact-open currying supplies uniform continuity here. -/
theorem vectorStopPath_continuous (T : ℝ≥0)
    (x : C(StrongSDEConcreteMaps.Window T, E)) :
    Continuous (fun t : ℝ≥0 => vectorStopPath T t x) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ℝ≥0 × StrongSDEConcreteMaps.Window T =>
    x (stopTime T p.1 p.2))
  apply x.continuous.comp
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_snd).min continuous_fst

def vectorStopPathLp (T t : ℝ≥0) :
    VectorPathLp (StrongSDEConcreteMaps.Window T) E μ →L[ℝ]
      VectorPathLp (StrongSDEConcreteMaps.Window T) E μ :=
  (vectorStopPath (E := E) T t).compLpL 2 μ

theorem vectorStopPathLp_ae (T t : ℝ≥0)
    (X : VectorPathLp (StrongSDEConcreteMaps.Window T) E μ) :
    (vectorStopPathLp T t X : Ω → C(StrongSDEConcreteMaps.Window T, E)) =ᵐ[μ]
      fun ω => vectorStopPath T t (X ω) := by
  have h := (vectorStopPath (E := E) T t).coeFn_compLpL (p := 2) (μ := μ) X
  filter_upwards [h] with ω hω
  exact hω

theorem vectorStopPathLp_norm_le (T t : ℝ≥0)
    (X : VectorPathLp (StrongSDEConcreteMaps.Window T) E μ) :
    ‖vectorStopPathLp T t X‖ ≤ ‖X‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [vectorStopPathLp_ae T t X] with ω hω
  rw [hω]
  exact vectorStopPath_norm_le T t _

theorem vectorStopPathLp_terminal (T : ℝ≥0)
    (X : VectorPathLp (StrongSDEConcreteMaps.Window T) E μ) :
    vectorStopPathLp T T X = X := by
  apply Lp.ext
  filter_upwards [vectorStopPathLp_ae T T X] with ω hω
  rw [hω, vectorStopPath_terminal]

/-- The norm-square formula does not require an inner product on the path
space. Apply the scalar L² formula to its pointwise norm instead. -/
theorem vectorPathLp_norm_sq (T : ℝ≥0)
    (X : VectorPathLp (StrongSDEConcreteMaps.Window T) E μ) :
    ‖X‖ ^ 2 = ∫ ω, ‖X ω‖ ^ 2 ∂μ := by
  let hm := (Lp.memLp X).norm
  let r : Lp ℝ 2 μ := hm.toLp (fun ω => ‖X ω‖)
  have hr : ‖r‖ = ‖X‖ := by
    have hae : ∀ᵐ ω ∂μ, ‖r ω‖ = ‖X ω‖ := by
      filter_upwards [hm.coeFn_toLp] with ω hω
      simp only [r, hω, norm_norm]
    exact le_antisymm
      (Lp.norm_le_norm_of_ae_le (hae.mono fun _ h => h.le))
      (Lp.norm_le_norm_of_ae_le (hae.mono fun _ h => h.ge))
  rw [← hr, lp_two_norm_sq]
  exact integral_congr_ae
    (hm.coeFn_toLp.mono fun _ h => congrArg (fun v : ℝ => v ^ 2) h)

/-- The actual running squared L² distance in the fixed finite-horizon carrier. -/
def runningProfile (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (X Y : State (E := E) (μ := μ) F T) (t : ℝ≥0) : ℝ :=
  ‖vectorStopPathLp T t (X.val - Y.val)‖ ^ 2

theorem runningProfile_nonneg (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (X Y : State (E := E) (μ := μ) F T) (t : ℝ≥0) :
    0 ≤ runningProfile F T X Y t := sq_nonneg _

theorem runningProfile_le_norm_sq (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (X Y : State (E := E) (μ := μ) F T) (t : ℝ≥0) :
    runningProfile F T X Y t ≤ ‖X - Y‖ ^ 2 := by
  have h := vectorStopPathLp_norm_le T t (X.val - Y.val)
  have hn := norm_nonneg (vectorStopPathLp T t (X.val - Y.val))
  change ‖vectorStopPathLp T t (X.val - Y.val)‖ ^ 2 ≤ ‖X.val - Y.val‖ ^ 2
  nlinarith [norm_nonneg (X.val - Y.val)]

theorem runningProfile_terminal (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (X Y : State (E := E) (μ := μ) F T) :
    runningProfile F T X Y T = ‖X - Y‖ ^ 2 := by
  change ‖vectorStopPathLp T T (X.val - Y.val)‖ ^ 2 = ‖X.val - Y.val‖ ^ 2
  rw [vectorStopPathLp_terminal]

theorem runningProfile_eq_integral (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (X Y : State (E := E) (μ := μ) F T) (t : ℝ≥0) :
    runningProfile F T X Y t =
      ∫ ω, ‖vectorStopPath T t
        (vectorRepresentative X.val ω - vectorRepresentative Y.val ω)‖ ^ 2 ∂μ := by
  rw [runningProfile, vectorPathLp_norm_sq]
  apply integral_congr_ae
  filter_upwards [vectorStopPathLp_ae T t (X.val - Y.val),
    Lp.coeFn_sub X.val Y.val, vectorRepresentative_ae X.val,
    vectorRepresentative_ae Y.val] with ω hs hsub hx hy
  rw [hs, hsub, Pi.sub_apply, hx, hy]

/-- The constructed profile is exactly the expectation of the squared path
supremum up to the requested time, in the original process realization. -/
theorem runningProfile_eq_expected_sup (F : Filtration ℝ≥0 mΩ) (T t : ℝ≥0)
    (ht : t ≤ T) (X Y : State (E := E) (μ := μ) F T) :
    runningProfile F T X Y t =
      ∫ ω, (⨆ s : StrongSDEConcreteMaps.Window t,
        ‖realize F T X s.val ω - realize F T Y s.val ω‖ ^ 2) ∂μ := by
  rw [runningProfile_eq_integral]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    let p := vectorRepresentative X.val ω - vectorRepresentative Y.val ω
    calc
      ‖vectorStopPath T t p‖ ^ 2 = ‖prefixPath ht p‖ ^ 2 :=
        congrArg (fun a : ℝ => a ^ 2) (vectorStopPath_norm_eq_prefixPath_norm ht p)
      _ = ⨆ s : StrongSDEConcreteMaps.Window t, ‖prefixPath ht p s‖ ^ 2 :=
        (vectorPath_sup_sq (prefixPath ht p)).symm
      _ = ⨆ s : StrongSDEConcreteMaps.Window t,
          ‖realize F T X s.val ω - realize F T Y s.val ω‖ ^ 2 := by
        apply congrArg (fun f : StrongSDEConcreteMaps.Window t → ℝ => ⨆ s, f s)
        funext s
        have hcap : cappedTime T s.val =
            (⟨s.val, s.property.1, s.property.2.trans ht⟩ :
              StrongSDEConcreteMaps.Window T) :=
          Subtype.ext (min_eq_left (s.property.2.trans ht))
        simp only [prefixPath_apply, p, ContinuousMap.sub_apply, realize, hcap]

theorem runningProfile_continuous (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (X Y : State (E := E) (μ := μ) F T) :
    Continuous (runningProfile F T X Y) := by
  have hm := (vectorRepresentative_memLp X.val).sub (vectorRepresentative_memLp Y.val)
  have hBound : Integrable (fun ω =>
      ‖vectorRepresentative X.val ω - vectorRepresentative Y.val ω‖ ^ 2) μ :=
    hm.norm.integrable_sq
  change Continuous (fun t : ℝ≥0 => runningProfile F T X Y t)
  simp_rw [runningProfile_eq_integral]
  apply continuous_of_dominated
    (bound := fun ω => ‖vectorRepresentative X.val ω - vectorRepresentative Y.val ω‖ ^ 2)
  · intro t
    exact ((continuous_norm.comp (vectorStopPath (E := E) T t).continuous).pow 2).comp_aestronglyMeasurable
      hm.aestronglyMeasurable
  · intro t
    exact ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h := vectorStopPath_norm_le T t
        (vectorRepresentative X.val ω - vectorRepresentative Y.val ω)
      nlinarith [norm_nonneg (vectorStopPath T t
        (vectorRepresentative X.val ω - vectorRepresentative Y.val ω)),
        norm_nonneg (vectorRepresentative X.val ω - vectorRepresentative Y.val ω)]
  · exact hBound
  · exact ae_of_all _ fun ω =>
      ((vectorStopPath_continuous T
        (vectorRepresentative X.val ω - vectorRepresentative Y.val ω)).norm).pow 2

/-- Continuity in the ordinary real-time parameter needed by the scalar
factorial engine. Before zero the stopping time is frozen at zero. -/
theorem runningProfile_real_continuous (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (X Y : State (E := E) (μ := μ) F T) :
    Continuous (fun t : ℝ => runningProfile F T X Y t.toNNReal) :=
  (runningProfile_continuous F T X Y).comp continuous_real_toNNReal

theorem runningProfile_integrable (F : Filtration ℝ≥0 mΩ) (T t : ℝ≥0)
    (X Y : State (E := E) (μ := μ) F T) :
    Integrable (runningProfile F T X Y) (timeMeasure_T t) := by
  change IntegrableOn (runningProfile F T X Y) (Ioc 0 t) timeMeasure
  exact (runningProfile_continuous F T X Y).integrableOn_Ioc

/-- Each time slice is bounded by the expected squared running norm up to that
same time. This is the bound used inside the coefficient-energy integral. -/
theorem runningProfile_slice_energy_le (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (X Y : State (E := E) (μ := μ) F T) (s : ℝ≥0) (hs : s ≤ T) :
    (∫ ω, ‖realize F T X s ω - realize F T Y s ω‖ ^ 2 ∂μ) ≤
      runningProfile F T X Y s := by
  let s' : StrongSDEConcreteMaps.Window T := ⟨s, zero_le, hs⟩
  have hcap : cappedTime T s = s' := Subtype.ext (min_eq_left hs)
  have hm := (vectorRepresentative_memLp X.val).sub (vectorRepresentative_memLp Y.val)
  have hBound := hm.norm.integrable_sq
  have hLeft : Integrable (fun ω =>
      ‖realize F T X s ω - realize F T Y s ω‖ ^ 2) μ := by
    refine hBound.mono' ?_ (ae_of_all _ fun ω => ?_)
    · have hc : Continuous (fun x : C(StrongSDEConcreteMaps.Window T, E) => ‖x s'‖ ^ 2) :=
        (continuous_norm.comp (ContinuousMap.evalCLM ℝ s').continuous).pow 2
      have hae := hc.comp_aestronglyMeasurable hm.aestronglyMeasurable
      simpa only [realize, hcap, ContinuousMap.sub_apply, Pi.sub_apply] using hae
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      change ‖vectorRepresentative X.val ω (cappedTime T s) -
        vectorRepresentative Y.val ω (cappedTime T s)‖ ^ 2 ≤ _
      rw [hcap]
      exact pow_le_pow_left₀ (norm_nonneg _)
        ((vectorRepresentative X.val ω - vectorRepresentative Y.val ω).norm_coe_le_norm s') 2
  have hRight : Integrable (fun ω => ‖vectorStopPath T s
      (vectorRepresentative X.val ω - vectorRepresentative Y.val ω)‖ ^ 2) μ := by
    refine hBound.mono' (((continuous_norm.comp
      (vectorStopPath (E := E) T s).continuous).pow 2).comp_aestronglyMeasurable
        hm.aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (vectorStopPath_norm_le T s _) 2
  rw [runningProfile_eq_integral]
  apply integral_mono hLeft hRight
  intro ω
  have h := vectorStopPath_eval_le T s
    (vectorRepresentative X.val ω - vectorRepresentative Y.val ω) s' le_rfl
  change ‖vectorRepresentative X.val ω (cappedTime T s) -
    vectorRepresentative Y.val ω (cappedTime T s)‖ ^ 2 ≤ _
  rw [hcap]
  change ‖(vectorRepresentative X.val ω - vectorRepresentative Y.val ω) s'‖ ^ 2 ≤ _
  nlinarith [norm_nonneg ((vectorRepresentative X.val ω - vectorRepresentative Y.val ω) s'),
    norm_nonneg (vectorStopPath T s
      (vectorRepresentative X.val ω - vectorRepresentative Y.val ω))]

/-- The installed nonnegative-time measure on a bounded interval is exactly
Lebesgue measure on the corresponding real interval under the inclusion. -/
theorem map_timeMeasure_T_coe (t : ℝ≥0) :
    Measure.map ((↑) : ℝ≥0 → ℝ) (timeMeasure_T t) =
      volume.restrict (Ioc (0 : ℝ) (t : ℝ)) := by
  have hPre : ((↑) : ℝ≥0 → ℝ) ⁻¹' Ioc (0 : ℝ) (t : ℝ) = Ioc 0 t := by
    ext s
    simp only [mem_preimage, mem_Ioc, NNReal.coe_pos, NNReal.coe_le_coe]
  calc
    Measure.map ((↑) : ℝ≥0 → ℝ) (timeMeasure_T t) =
        (Measure.map ((↑) : ℝ≥0 → ℝ) timeMeasure).restrict (Ioc 0 (t : ℝ)) := by
      change Measure.map ((↑) : ℝ≥0 → ℝ) (timeMeasure.restrict (Ioc 0 t)) = _
      rw [measurableEmbedding_nnrealCoe.restrict_map, hPre]
    _ = (volume.restrict (range ((↑) : ℝ≥0 → ℝ))).restrict (Ioc 0 (t : ℝ)) := by
      rw [timeMeasure, measurableEmbedding_nnrealCoe.map_comap]
    _ = volume.restrict (Ioc 0 (t : ℝ)) := by
      apply Measure.restrict_restrict_of_subset
      intro s hs
      exact ⟨⟨s, le_of_lt hs.1⟩, rfl⟩

/-- Conversion for every integrand; no integrability premise is needed because
the measurable-embedding change-of-variables theorem also covers the default
value of the Bochner integral. -/
theorem integral_timeMeasure_T_eq_intervalIntegral (t : ℝ≥0) (f : ℝ≥0 → ℝ) :
    (∫ s, f s ∂timeMeasure_T t) =
      ∫ s in (0 : ℝ)..(t : ℝ), f s.toNNReal := by
  calc
    (∫ s, f s ∂timeMeasure_T t) =
        ∫ s : ℝ, f s.toNNReal
          ∂(Measure.map ((↑) : ℝ≥0 → ℝ) (timeMeasure_T t)) := by
      rw [measurableEmbedding_nnrealCoe.integral_map]
      simp only [Real.toNNReal_coe]
    _ = ∫ s in (0 : ℝ)..(t : ℝ), f s.toNNReal := by
      rw [map_timeMeasure_T_coe, intervalIntegral.integral_of_le t.coe_nonneg]

/-- With the actual running profile constructed, the sole analytic premise for
the global fixed-point engine is the time-local Volterra estimate for the
chosen self-map. Its integral uses the installed predictable-time measure. -/
theorem exists_unique_of_runningProfile_volterra
    (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (Φ : State (E := E) (μ := μ) F T → State (E := E) (μ := μ) F T)
    {K : ℝ} (hK : 0 ≤ K)
    (hVolterra : ∀ X Y t, t ≤ T →
      runningProfile F T (Φ X) (Φ Y) t ≤
        K * ∫ s, runningProfile F T X Y s ∂timeMeasure_T t) :
    ∃! X, Φ X = X := by
  letI := state_complete (E := E) (μ := μ) F T
  apply StrongSDE.exists_unique_of_volterra_profile Φ
    (fun X Y t => runningProfile F T X Y t.toNNReal) T.coe_nonneg hK
  · intro X Y
    exact (runningProfile_real_continuous F T X Y).continuousOn
  · intro X Y t _
    exact runningProfile_le_norm_sq F T X Y t.toNNReal
  · intro X Y
    simpa only [Real.toNNReal_coe] using runningProfile_terminal F T X Y
  · intro X Y t ht
    have htle : t.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr ht.2
    have h := hVolterra X Y t.toNNReal htle
    rw [integral_timeMeasure_T_eq_intervalIntegral] at h
    simpa only [Real.coe_toNNReal t ht.1] using h

end Ripple.Stochastic.StrongSDERunningMoment
