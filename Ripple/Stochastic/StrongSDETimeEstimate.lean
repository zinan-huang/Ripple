import Ripple.Stochastic.StoppedContinuousIto
import Ripple.Stochastic.StrongSDEConcreteMaps
import Ripple.Stochastic.StrongSDERunningMoment

/-!
# Local energy estimates for the concrete Picard coefficients

The noise uses the actual `channelIntegral` and its installed
predictable L² input. Deterministic time clipping is admissible even though it
introduces a jump. The local energy is integrated in time before any estimate
by the terminal running maximum is made.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace Ripple.Stochastic.StrongSDETimeEstimate
open AdaptedContinuousSpace ContinuousAdaptedIntegrand ContinuousItoElementary
open FilteredItoIntegralL2 FilteredItoIntegralCLM FilteredItoIntegralProcessGeneral
open StrongSDEConcreteMaps StrongSDERunningMoment

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Restricting the larger predictable measure to a smaller time band gives
exactly the installed smaller-horizon measure. -/
theorem trimMeasure_restrict_timeBand {F : Filtration ℝ≥0 mΩ}
    {B : ℝ≥0 → Ω → ℝ} {T t : ℝ≥0} (ht : t ≤ T)
    (hBmeas : ∀ u, Measurable (B u)) :
    (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas).restrict
      (StoppedContinuousIto.timeBand t) = trimMeasure_T (𝓖 := F) (μ := μ) t hBmeas := by
  rw [trimMeasure_T_eq_restrict (𝓖 := F) T hBmeas, StoppedContinuousIto.timeBand,
    Measure.restrict_restrict_of_subset
      (Set.prod_mono (Set.Ioc_subset_Ioc le_rfl ht) subset_rfl),
    trimMeasure_T_eq_restrict (𝓖 := F) t hBmeas]

section Scalar
variable {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
  [IsFilteredPreBrownian B F μ]

/-- Fubini identifies the clipped predictable input's energy with the actual
coefficient-difference energy on the smaller interval. -/
theorem coefficient_sub_band_energy (T t : ℝ≥0) (ht : t ≤ T)
    (hBmeas : ∀ u, Measurable (B u)) (H G : ℝ≥0 → Ω → ℝ)
    (haH : ∀ s, Measurable[F s] (H s)) (haG : ∀ s, Measurable[F s] (G s))
    (hcH : ∀ ω, Continuous (fun s => H s ω))
    (hcG : ∀ ω, Continuous (fun s => G s ω)) (KH KG : ℝ)
    (hbH : ∀ s ω, |H s ω| ≤ KH) (hbG : ∀ s ω, |G s ω| ≤ KG) :
    (∫ z in StoppedContinuousIto.timeBand t,
      ((integrandLp (μ := μ) T hBmeas H haH hcH KH hbH -
        integrandLp (μ := μ) T hBmeas G haG hcG KG hbG) z) ^ 2
      ∂(trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) =
      ∫ s, ∫ ω, (H s ω - G s ω) ^ 2 ∂μ ∂timeMeasure_T t := by
  have hae : (fun z => ((integrandLp (μ := μ) T hBmeas H haH hcH KH hbH -
      integrandLp (μ := μ) T hBmeas G haG hcG KG hbG) z) ^ 2)
      =ᵐ[trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas]
        fun z => (H z.1 z.2 - G z.1 z.2) ^ 2 := by
    filter_upwards [Lp.coeFn_sub (integrandLp (μ := μ) T hBmeas H haH hcH KH hbH)
      (integrandLp (μ := μ) T hBmeas G haG hcG KG hbG),
      integrandLp_coe (μ := μ) T hBmeas H haH hcH KH hbH,
      integrandLp_coe (μ := μ) T hBmeas G haG hcG KG hbG] with z hsub hH hG
    rw [hsub, Pi.sub_apply, hH, hG]
    rfl
  rw [integral_congr_ae (ae_restrict_of_ae hae)]
  change (∫ z, (H z.1 z.2 - G z.1 z.2) ^ 2
    ∂((trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas).restrict
      (StoppedContinuousIto.timeBand t))) = _
  rw [trimMeasure_restrict_timeBand ht hBmeas]
  have hsm : StronglyMeasurable[F.predictable]
      (fun z : ℝ≥0 × Ω => (H z.1 z.2 - G z.1 z.2) ^ 2) :=
    ((stronglyMeasurable_uncurry haH hcH).sub (stronglyMeasurable_uncurry haG hcG)).pow 2
  rw [show trimMeasure_T (𝓖 := F) (μ := μ) t hBmeas =
      ((timeMeasure_T t).prod μ).trim F.predictable_le_prod from rfl,
    ← integral_trim F.predictable_le_prod hsm]
  have hm : MemLp (fun z : ℝ≥0 × Ω => H z.1 z.2 - G z.1 z.2) 2
      ((timeMeasure_T t).prod μ) := by
    apply MemLp.of_bound
      (((stronglyMeasurable_uncurry haH hcH).sub
        (stronglyMeasurable_uncurry haG hcG)).mono
          F.predictable_le_prod).aestronglyMeasurable (KH + KG)
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]
      exact (abs_sub _ _).trans (add_le_add (hbH _ _) (hbG _ _))
  exact integral_prod _ hm.integrable_sq

/-- Scalar local maximal estimate, before substituting the SDE coefficients. -/
theorem stopped_integrand_sub_norm_sq_le (T t : ℝ≥0) (ht : t ≤ T)
    (hB : ∀ ω, Continuous (fun s => B s ω)) (hBmeas : ∀ u, Measurable (B u))
    (H G : ℝ≥0 → Ω → ℝ)
    (haH : ∀ s, Measurable[F s] (H s)) (haG : ∀ s, Measurable[F s] (G s))
    (hcH : ∀ ω, Continuous (fun s => H s ω))
    (hcG : ∀ ω, Continuous (fun s => G s ω)) (KH KG : ℝ)
    (hbH : ∀ s ω, |H s ω| ≤ KH) (hbG : ∀ s ω, |G s ω| ≤ KG) :
    ‖StoppedContinuousIto.stopPathLp T t
      (continuousIto T hB hBmeas (integrandLp (μ := μ) T hBmeas H haH hcH KH hbH) -
       continuousIto T hB hBmeas (integrandLp (μ := μ) T hBmeas G haG hcG KG hbG))‖ ^ 2 ≤
      4 * ∫ s, ∫ ω, (H s ω - G s ω) ^ 2 ∂μ ∂timeMeasure_T t := by
  rw [← map_sub]
  exact (StoppedContinuousIto.stopped_continuousIto_norm_sq_le T t hB hBmeas
    (integrandLp (μ := μ) T hBmeas H haH hcH KH hbH -
      integrandLp (μ := μ) T hBmeas G haG hcG KG hbG)).trans_eq
    (congrArg (fun a : ℝ => 4 * a)
      (coefficient_sub_band_energy T t ht hBmeas H G haH haG hcH hcG KH KG hbH hbG))

end Scalar

/-- Integral Cauchy--Schwarz on a finite measure, proved by integrating a square.
The zero-mass case is supplied separately by the caller. -/
theorem integral_sq_le_mass_mul_integral_sq {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] (f : α → ℝ)
    (hf : Integrable f ν) (hf_sq : Integrable (fun a => (f a) ^ 2) ν)
    (hm : 0 < ν.real univ) :
    (∫ a, f a ∂ν) ^ 2 ≤ ν.real univ * ∫ a, (f a) ^ 2 ∂ν := by
  let m := ν.real univ
  let a := ∫ z, f z ∂ν
  let b := ∫ z, (f z) ^ 2 ∂ν
  have h1 : Integrable (fun z => m ^ 2 * (f z) ^ 2) ν := hf_sq.const_mul _
  have h2 : Integrable (fun z => (2 * m * a) * f z) ν := hf.const_mul _
  have h12 : Integrable (fun z => m ^ 2 * (f z) ^ 2 - (2 * m * a) * f z) ν := h1.sub h2
  have hpos : 0 ≤ ∫ z, m ^ 2 * (f z) ^ 2 - (2 * m * a) * f z + a ^ 2 ∂ν := by
    apply integral_nonneg
    intro z
    show 0 ≤ m ^ 2 * (f z) ^ 2 - (2 * m * a) * f z + a ^ 2
    nlinarith [sq_nonneg (m * f z - a)]
  rw [integral_add h12 (integrable_const _),
    integral_sub h1 h2,
    integral_const_mul, integral_const_mul, integral_const, smul_eq_mul] at hpos
  change 0 ≤ m ^ 2 * b - (2 * m * a) * a + m * a ^ 2 at hpos
  have hmul : 0 ≤ m * (m * b - a ^ 2) := by nlinarith
  have hdiff : 0 ≤ m * b - a ^ 2 := by nlinarith
  change a ^ 2 ≤ m * b
  linarith

section Drift

/-- For a fixed pair of continuous paths, Cauchy--Schwarz in time controls the
stopped drift by the integral of the squared running input distance. -/
theorem driftPath_local_sq_le (T t : ℝ≥0) (ht : t ≤ T)
    (b : E → E) {L : ℝ≥0} (hb : LipschitzWith L b)
    (x y : C(StrongSDEConcreteMaps.Window T, E)) :
    ‖vectorStopPath T t (driftPath T b hb.continuous x -
      driftPath T b hb.continuous y)‖ ^ 2 ≤
      (t : ℝ) * (L : ℝ) ^ 2 *
        ∫ s in (0 : ℝ)..(t : ℝ), ‖vectorStopPath T s.toNNReal (x - y)‖ ^ 2 := by
  by_cases htzero : t = 0
  · subst t
    have hz : vectorStopPath T 0 (driftPath T b hb.continuous x -
        driftPath T b hb.continuous y) = 0 := by
      ext u
      simp [vectorStopPath_apply, StoppedContinuousIto.stopTime, driftPath]
    simp [hz]
  have htpos : 0 < (t : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr htzero)
  let R : ℝ → ℝ := fun s => ‖vectorStopPath T s.toNNReal (x - y)‖
  let f : ℝ → ℝ := fun s => (L : ℝ) * R s
  let ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (t : ℝ))
  have hR : Continuous R :=
    ((vectorStopPath_continuous T (x - y)).comp continuous_real_toNNReal).norm
  have hf : Continuous f := continuous_const.mul hR
  have hfInt : Integrable f ν := hf.integrableOn_Ioc
  have hfSq : Integrable (fun s => (f s) ^ 2) ν := (hf.pow 2).integrableOn_Ioc
  have hfnonneg : ∀ s, 0 ≤ f s := fun s => mul_nonneg L.coe_nonneg (norm_nonneg _)
  have hmass : ν.real univ = (t : ℝ) := by
    simp [ν, Measure.real_def, Real.volume_Ioc, ENNReal.toReal_ofReal t.coe_nonneg]
  have hCauchy := integral_sq_le_mass_mul_integral_sq ν f hfInt hfSq (by rw [hmass]; exact htpos)
  rw [hmass] at hCauchy
  have hpath : ‖vectorStopPath T t (driftPath T b hb.continuous x -
      driftPath T b hb.continuous y)‖ ≤ ∫ s, f s ∂ν := by
    apply (ContinuousMap.norm_le _ (integral_nonneg hfnonneg)).mpr
    intro u
    let v := StoppedContinuousIto.stopTime T t u
    have hvt : v.val ≤ t := min_le_right _ _
    have hbInt : IntervalIntegrable (fun s => b (x (realTime T s))) volume 0 (v.val : ℝ) :=
      (hb.continuous.comp (x.continuous.comp (realTime_continuous T))).intervalIntegrable _ _
    have hbInt' : IntervalIntegrable (fun s => b (y (realTime T s))) volume 0 (v.val : ℝ) :=
      (hb.continuous.comp (y.continuous.comp (realTime_continuous T))).intervalIntegrable _ _
    change ‖(∫ s in (0 : ℝ)..(v.val : ℝ), b (x (realTime T s))) -
      ∫ s in (0 : ℝ)..(v.val : ℝ), b (y (realTime T s))‖ ≤ _
    rw [← intervalIntegral.integral_sub hbInt hbInt',
      intervalIntegral.integral_of_le v.val.coe_nonneg]
    calc
      _ ≤ ∫ s in Ioc (0 : ℝ) (v.val : ℝ),
          ‖b (x (realTime T s)) - b (y (realTime T s))‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ s in Ioc (0 : ℝ) (v.val : ℝ), f s := by
        apply setIntegral_mono_on
          ((hbInt.sub hbInt').1.norm) hf.integrableOn_Ioc measurableSet_Ioc
        intro s hs
        have hst : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr
          (hs.2.trans (by exact_mod_cast v.property.2))
        have heq : StoppedContinuousIto.stopTime T s.toNNReal (realTime T s) = realTime T s := by
          apply Subtype.ext
          change min (min s.toNNReal T) s.toNNReal = min s.toNNReal T
          rw [min_eq_left hst, min_self]
        have hev : ‖x (realTime T s) - y (realTime T s)‖ ≤ R s := by
          have h := (vectorStopPath T s.toNNReal (x - y)).norm_coe_le_norm (realTime T s)
          simpa only [vectorStopPath_apply, heq, ContinuousMap.sub_apply, R] using h
        have hd := hb.dist_le_mul (x (realTime T s)) (y (realTime T s))
        rw [dist_eq_norm, dist_eq_norm] at hd
        exact hd.trans (mul_le_mul_of_nonneg_left hev L.coe_nonneg)
      _ ≤ ∫ s, f s ∂ν := by
        apply setIntegral_mono_set hfInt
        · exact ae_of_all _ hfnonneg
        · exact ae_of_all _ fun s hs => Ioc_subset_Ioc le_rfl (by exact_mod_cast hvt) hs
  have hsquare := mul_self_le_mul_self (norm_nonneg _) hpath
  have heq : (∫ s, (f s) ^ 2 ∂ν) =
      (L : ℝ) ^ 2 * ∫ s in (0 : ℝ)..(t : ℝ), (R s) ^ 2 := by
    simp only [f, mul_pow, integral_const_mul,
      intervalIntegral.integral_of_le t.coe_nonneg, ν]
  rw [heq] at hCauchy
  change ‖vectorStopPath T t (driftPath T b hb.continuous x -
    driftPath T b hb.continuous y)‖ ^ 2 ≤ (t : ℝ) * (L : ℝ) ^ 2 * ∫ s in 0..(t : ℝ), (R s) ^ 2
  nlinarith

/-- The concrete drift map satisfies the local energy estimate on its actual
continuous adapted L² carrier. -/
theorem drift_local_sq_le (F : Filtration ℝ≥0 mΩ) (T t : ℝ≥0) (ht : t ≤ T)
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (b : E → E) {L : ℝ≥0} (hb : LipschitzWith L b)
    (C : ℝ) (hC : 0 ≤ C) (hbC : ∀ x, ‖b x‖ ≤ C)
    (X Y : State (E := E) (μ := μ) F T) :
    runningProfile F T (drift F T hnull b hb C hC hbC X)
      (drift F T hnull b hb C hC hbC Y) t ≤
      (T : ℝ) * (L : ℝ) ^ 2 * ∫ s, runningProfile F T X Y s ∂timeMeasure_T t := by
  let D := fun ω => vectorRepresentative X.val ω - vectorRepresentative Y.val ω
  let R := fun (s : ℝ) ω => ‖vectorStopPath T s.toNNReal (D ω)‖ ^ 2
  let ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (t : ℝ))
  have hD : MemLp D 2 μ :=
    (vectorRepresentative_memLp X.val).sub (vectorRepresentative_memLp Y.val)
  have hfull : Integrable (fun ω => ‖D ω‖ ^ 2) μ := hD.norm.integrable_sq
  have hsm : StronglyMeasurable (Function.uncurry R) := by
    apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    · intro ω
      exact (((vectorStopPath_continuous T (D ω)).comp continuous_real_toNNReal).norm).pow 2
    · intro s
      exact (((vectorStopPath T s.toNNReal).continuous.comp_stronglyMeasurable
        ((vectorRepresentative_stronglyMeasurable X.val).sub
          (vectorRepresentative_stronglyMeasurable Y.val))).norm).pow 2
  have hprod : Integrable (Function.uncurry R) (ν.prod μ) := by
    apply (hfull.comp_snd ν).mono' hsm.aestronglyMeasurable
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (vectorStopPath_norm_le T z.1.toNNReal (D z.2)) 2
  have hFubini : (∫ ω, ∫ s, R s ω ∂ν ∂μ) =
      ∫ s, runningProfile F T X Y s.toNNReal ∂ν := by
    rw [← integral_integral_swap hprod]
    apply integral_congr_ae
    exact ae_of_all _ fun s => (runningProfile_eq_integral F T X Y s.toNNReal).symm
  have hleft : runningProfile F T (drift F T hnull b hb C hC hbC X)
      (drift F T hnull b hb C hC hbC Y) t =
      ∫ ω, ‖vectorStopPath T t
        (driftPath T b hb.continuous (vectorRepresentative X.val ω) -
          driftPath T b hb.continuous (vectorRepresentative Y.val ω))‖ ^ 2 ∂μ := by
    rw [runningProfile, vectorPathLp_norm_sq]
    apply integral_congr_ae
    filter_upwards [vectorStopPathLp_ae T t
      ((drift F T hnull b hb C hC hbC X).val - (drift F T hnull b hb C hC hbC Y).val),
      Lp.coeFn_sub (drift F T hnull b hb C hC hbC X).val (drift F T hnull b hb C hC hbC Y).val,
      drift_coe F T hnull b hb C hC hbC X,
      drift_coe F T hnull b hb C hC hbC Y] with ω hs hsub hx hy
    rw [hs, hsub, Pi.sub_apply, hx, hy]
  have hleftInt : Integrable (fun ω => ‖vectorStopPath T t
      (driftPath T b hb.continuous (vectorRepresentative X.val ω) -
        driftPath T b hb.continuous (vectorRepresentative Y.val ω))‖ ^ 2) μ := by
    have hm := (driftPath_memLp F T b hb C hC hbC X).sub (driftPath_memLp F T b hb C hC hbC Y)
    refine hm.norm.integrable_sq.mono' (((continuous_norm.comp
      (vectorStopPath (E := E) T t).continuous).pow 2).comp_aestronglyMeasurable
        hm.aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (vectorStopPath_norm_le T t _) 2
  have hpoint : runningProfile F T (drift F T hnull b hb C hC hbC X)
      (drift F T hnull b hb C hC hbC Y) t ≤
      (t : ℝ) * (L : ℝ) ^ 2 * ∫ s, runningProfile F T X Y s ∂timeMeasure_T t := by
    rw [hleft, integral_timeMeasure_T_eq_intervalIntegral,
      intervalIntegral.integral_of_le t.coe_nonneg]
    have hi := integral_mono hleftInt
      (hprod.integral_prod_right.const_mul ((t : ℝ) * (L : ℝ) ^ 2))
      (fun ω => by
        simpa only [intervalIntegral.integral_of_le t.coe_nonneg, D, R, ν] using
          driftPath_local_sq_le T t ht b hb
            (vectorRepresentative X.val ω) (vectorRepresentative Y.val ω))
    rw [integral_const_mul] at hi
    simp only [Function.uncurry_apply_pair] at hi
    rw [hFubini] at hi
    exact hi
  exact hpoint.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by exact_mod_cast ht) (sq_nonneg _))
    (integral_nonneg (runningProfile_nonneg F T X Y)))

end Drift

section ConcreteNoise
variable {ι : Type*} [Fintype ι]
  (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
  (B : ι → ℝ≥0 → Ω → ℝ) [∀ i, IsFilteredPreBrownian (B i) F μ]
  (hB : ∀ i ω, Continuous (fun s => B i s ω))
  (hBmeas : ∀ i s, Measurable (B i s))
  (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
  (ell : ι → E) (g : ι → E → ℝ) (L : ι → ℝ≥0)
  (hLip : ∀ i, LipschitzWith (L i) (g i)) (K : ι → ℝ)
  (hK : ∀ i x, |g i x| ≤ K i)

include hnull hLip K hK in
/-- At a fixed time, the actual coefficient difference is controlled by the
stopped representative of the input-path difference. -/
theorem coefficient_slice_energy_le
    (X Y : State (E := E) (μ := μ) F T) (i : ι) (s : ℝ≥0) (hs : s ≤ T) :
    (∫ ω, (g i (realize F T X s ω) - g i (realize F T Y s ω)) ^ 2 ∂μ) ≤
      (L i : ℝ) ^ 2 * runningProfile F T X Y s := by
  let R := fun ω => vectorStopPath T s
    (vectorRepresentative X.val ω - vectorRepresentative Y.val ω)
  have hDm := (vectorRepresentative_memLp X.val).sub (vectorRepresentative_memLp Y.val)
  have hRsq : Integrable (fun ω => ‖R ω‖ ^ 2) μ := by
    refine hDm.norm.integrable_sq.mono' (((continuous_norm.comp
      (vectorStopPath (E := E) T s).continuous).pow 2).comp_aestronglyMeasurable
        hDm.aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (vectorStopPath_norm_le T s _) 2
  have hcoeff : MemLp
      (fun ω => g i (realize F T X s ω) - g i (realize F T Y s ω)) 2 μ := by
    apply MemLp.of_bound
      (((hLip i).continuous.measurable.comp
        ((realize_adapted F T hnull X s).measurable.mono (F.le s) le_rfl)).sub
       ((hLip i).continuous.measurable.comp
        ((realize_adapted F T hnull Y s).measurable.mono (F.le s) le_rfl))).aestronglyMeasurable
      (K i + K i)
    exact ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]
      exact (abs_sub _ _).trans (add_le_add (hK i _) (hK i _))
  rw [runningProfile_eq_integral, ← integral_const_mul]
  apply integral_mono hcoeff.integrable_sq (hRsq.const_mul _)
  intro ω
  let u : StrongSDEConcreteMaps.Window T := ⟨s, zero_le, hs⟩
  have hstop : StoppedContinuousIto.stopTime T s u = u :=
    Subtype.ext (min_self s)
  have hcap : cappedTime T s = u := Subtype.ext (min_eq_left hs)
  have heval : ‖realize F T X s ω - realize F T Y s ω‖ ≤ ‖R ω‖ := by
    have he := (R ω).norm_coe_le_norm u
    simpa only [R, vectorStopPath_apply, hstop, ContinuousMap.sub_apply,
      realize, hcap] using he
  have hLip' : |g i (realize F T X s ω) - g i (realize F T Y s ω)| ≤
      (L i : ℝ) * ‖R ω‖ := by
    have hd := (hLip i).dist_le_mul (realize F T X s ω) (realize F T Y s ω)
    rw [Real.dist_eq, dist_eq_norm] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left heval (L i).coe_nonneg)
  have hsq := mul_self_le_mul_self (abs_nonneg _) hLip'
  nlinarith [sq_abs (g i (realize F T X s ω) - g i (realize F T Y s ω))]

/-- Local Doob estimate for an actual installed scalar channel integral. -/
theorem channelIntegral_local_sq_le (t : ℝ≥0) (ht : t ≤ T)
    (X Y : State (E := E) (μ := μ) F T) (i : ι) :
    ‖StoppedContinuousIto.stopPathLp T t
      (channelIntegral F T B hB hBmeas hnull g (fun i => (hLip i).continuous) K hK X i -
       channelIntegral F T B hB hBmeas hnull g (fun i => (hLip i).continuous) K hK Y i)‖ ^ 2 ≤
      4 * (L i : ℝ) ^ 2 * ∫ s, runningProfile F T X Y s ∂timeMeasure_T t := by
  let H := fun s ω => g i (realize F T X s ω)
  let G := fun s ω => g i (realize F T Y s ω)
  have haH : ∀ s, Measurable[F s] (H s) :=
    measurable_comp_sections (fun s => (realize_adapted F T hnull X s).measurable)
      (hLip i).continuous
  have haG : ∀ s, Measurable[F s] (G s) :=
    measurable_comp_sections (fun s => (realize_adapted F T hnull Y s).measurable)
      (hLip i).continuous
  have hcH : ∀ ω, Continuous (fun s => H s ω) :=
    continuous_comp_paths (realize_continuous F T X) (hLip i).continuous
  have hcG : ∀ ω, Continuous (fun s => G s ω) :=
    continuous_comp_paths (realize_continuous F T Y) (hLip i).continuous
  have hlocal := stopped_integrand_sub_norm_sq_le (μ := μ) T t ht (hB i) (hBmeas i)
    H G haH haG hcH hcG (K i) (K i) (fun _ _ => hK i _) (fun _ _ => hK i _)
  change ‖StoppedContinuousIto.stopPathLp T t
    (channelIntegral F T B hB hBmeas hnull g (fun i => (hLip i).continuous) K hK X i -
     channelIntegral F T B hB hBmeas hnull g (fun i => (hLip i).continuous) K hK Y i)‖ ^ 2 ≤
      4 * ∫ s, ∫ ω, (H s ω - G s ω) ^ 2 ∂μ ∂timeMeasure_T t at hlocal
  have hm : MemLp (fun z : ℝ≥0 × Ω => H z.1 z.2 - G z.1 z.2) 2
      ((timeMeasure_T t).prod μ) := by
    apply MemLp.of_bound
      (((stronglyMeasurable_uncurry haH hcH).sub
        (stronglyMeasurable_uncurry haG hcG)).mono
          F.predictable_le_prod).aestronglyMeasurable (K i + K i)
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]
      exact (abs_sub _ _).trans (add_le_add (hK i _) (hK i _))
  have he : (∫ s, ∫ ω, (H s ω - G s ω) ^ 2 ∂μ ∂timeMeasure_T t) ≤
      (L i : ℝ) ^ 2 * ∫ s, runningProfile F T X Y s ∂timeMeasure_T t := by
    rw [← integral_const_mul]
    apply integral_mono_ae hm.integrable_sq.integral_prod_left
      ((runningProfile_integrable F T t X Y).const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact coefficient_slice_energy_le F T hnull g L hLip K hK X Y i s (hs.2.trans ht)
  exact hlocal.trans (by nlinarith)

end ConcreteNoise

/-- Deterministic stopping commutes with embedding a scalar path in a fixed
direction of the state space. -/
theorem vectorStop_directionPathLp (T t : ℝ≥0) (v : E)
    (U : PathLp (StrongSDEConcreteMaps.Window T) μ) :
    vectorStopPathLp T t (directionPathLp v U) =
      directionPathLp v (StoppedContinuousIto.stopPathLp T t U) := by
  apply Lp.ext
  filter_upwards [vectorStopPathLp_ae T t (directionPathLp v U),
    directionPathLp_ae v U,
    directionPathLp_ae v (StoppedContinuousIto.stopPathLp T t U),
    StoppedContinuousIto.stopPathLp_ae T t U] with ω hs hd hv hu
  rw [hs, hd, hv, hu]
  apply ContinuousMap.ext
  intro s
  rfl

section SumNoise
variable {ι : Type*} [Fintype ι]
  (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
  (B : ι → ℝ≥0 → Ω → ℝ) [∀ i, IsFilteredPreBrownian (B i) F μ]
  (hB : ∀ i ω, Continuous (fun s => B i s ω))
  (hBmeas : ∀ i s, Measurable (B i s))
  (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
  (ell : ι → E) (g : ι → E → ℝ) (L : ι → ℝ≥0)
  (hLip : ∀ i, LipschitzWith (L i) (g i)) (K : ι → ℝ)
  (hK : ∀ i x, |g i x| ≤ K i)

/-- Finite-channel local energy with the sum of channel Lipschitz weights.
Triangle inequality in the genuine L² path space retains the sharp weight
sum and requires no independence between the channel integrals. -/
theorem noise_local_sq_le (t : ℝ≥0) (ht : t ≤ T)
    (N : ℕ) (hN : 1 ≤ N) (X Y : State (E := E) (μ := μ) F T) :
    runningProfile F T
      (noise F T B hB hBmeas hnull ell g (fun i => (hLip i).continuous) K hK N X)
      (noise F T B hB hBmeas hnull ell g (fun i => (hLip i).continuous) K hK N Y) t ≤
      4 * (∑ i, ‖ell i‖ * (L i : ℝ)) ^ 2 *
        ∫ s, runningProfile F T X Y s ∂timeMeasure_T t := by
  classical
  let A := ∫ s, runningProfile F T X Y s ∂timeMeasure_T t
  have hA : 0 ≤ A := integral_nonneg (runningProfile_nonneg F T X Y)
  let J := fun i => channelIntegral F T B hB hBmeas hnull g
    (fun i => (hLip i).continuous) K hK X i -
      channelIntegral F T B hB hBmeas hnull g
        (fun i => (hLip i).continuous) K hK Y i
  let a := (Real.sqrt (N : ℝ))⁻¹
  have ha := StrongSDE.inverse_sqrt_nat_bounds hN
  have hchannel : ∀ i, ‖StoppedContinuousIto.stopPathLp T t (J i)‖ ≤
      2 * (L i : ℝ) * Real.sqrt A := by
    intro i
    have h := channelIntegral_local_sq_le F T B hB hBmeas hnull g L hLip K hK t ht X Y i
    change ‖StoppedContinuousIto.stopPathLp T t (J i)‖ ^ 2 ≤ 4 * (L i : ℝ) ^ 2 * A at h
    have hnonneg : 0 ≤ 2 * (L i : ℝ) * Real.sqrt A := by positivity
    have heq : (2 * (L i : ℝ) * Real.sqrt A) ^ 2 = 4 * (L i : ℝ) ^ 2 * A := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hA]
      ring
    nlinarith [norm_nonneg (StoppedContinuousIto.stopPathLp T t (J i))]
  have hnorm : ‖vectorStopPathLp T t
      ((noise F T B hB hBmeas hnull ell g (fun i => (hLip i).continuous) K hK N X).val -
       (noise F T B hB hBmeas hnull ell g (fun i => (hLip i).continuous) K hK N Y).val)‖ ≤
      2 * (∑ i, ‖ell i‖ * (L i : ℝ)) * Real.sqrt A := by
    change ‖vectorStopPathLp T t
      ((∑ i, a • directionPathLp (ell i) (channelIntegral F T B hB hBmeas hnull g
          (fun i => (hLip i).continuous) K hK X i)) -
       ∑ i, a • directionPathLp (ell i) (channelIntegral F T B hB hBmeas hnull g
          (fun i => (hLip i).continuous) K hK Y i))‖ ≤ _
    rw [← Finset.sum_sub_distrib, map_sum]
    calc
      _ ≤ ∑ i, ‖vectorStopPathLp T t
          (a • directionPathLp (ell i) (channelIntegral F T B hB hBmeas hnull g
              (fun i => (hLip i).continuous) K hK X i) -
           a • directionPathLp (ell i) (channelIntegral F T B hB hBmeas hnull g
              (fun i => (hLip i).continuous) K hK Y i))‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖ell i‖ * (2 * (L i : ℝ) * Real.sqrt A) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [← smul_sub, ← map_sub, map_smul, vectorStop_directionPathLp,
          norm_smul, Real.norm_eq_abs, abs_of_nonneg ha.1]
        calc
          _ ≤ ‖directionPathLp (ell i) (StoppedContinuousIto.stopPathLp T t (J i))‖ := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right ha.2 (norm_nonneg _)
          _ ≤ ‖ell i‖ * ‖StoppedContinuousIto.stopPathLp T t (J i)‖ := directionPathLp_norm_le _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left (hchannel i) (norm_nonneg _)
      _ = _ := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  change ‖vectorStopPathLp T t _‖ ^ 2 ≤ 4 * (∑ i, ‖ell i‖ * (L i : ℝ)) ^ 2 * A
  have hsq := mul_self_le_mul_self (norm_nonneg _) hnorm
  have heq : (2 * (∑ i, ‖ell i‖ * (L i : ℝ)) * Real.sqrt A) ^ 2 =
      4 * (∑ i, ‖ell i‖ * (L i : ℝ)) ^ 2 * A := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hA]
    ring
  nlinarith

end SumNoise

/-- The time-local Volterra estimate for the actual drift and finite-channel
noise maps, on an arbitrary finite horizon. -/
theorem picardStep_local_sq_le {ι : Type*} [Fintype ι]
    (F : Filtration ℝ≥0 mΩ) (T t : ℝ≥0) (ht : t ≤ T)
    (B : ι → ℝ≥0 → Ω → ℝ) [∀ i, IsFilteredPreBrownian (B i) F μ]
    (hB : ∀ i ω, Continuous (fun s => B i s ω))
    (hBmeas : ∀ i s, Measurable (B i s))
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (ell : ι → E) (g : ι → E → ℝ) (L : ι → ℝ≥0)
    (hLip : ∀ i, LipschitzWith (L i) (g i)) (K : ι → ℝ)
    (hK : ∀ i x, |g i x| ≤ K i)
    (b : E → E) (Lb : ℝ≥0) (hb : LipschitzWith Lb b)
    (C : ℝ) (hC : 0 ≤ C) (hbC : ∀ x, ‖b x‖ ≤ C)
    (X₀ : State (E := E) (μ := μ) F T) (N : ℕ) (hN : 1 ≤ N)
    (X Y : State (E := E) (μ := μ) F T) :
    runningProfile F T
      (StrongSDE.picardStep X₀ (drift F T hnull b hb C hC hbC)
        (noise F T B hB hBmeas hnull ell g (fun i => (hLip i).continuous) K hK N) X)
      (StrongSDE.picardStep X₀ (drift F T hnull b hb C hC hbC)
        (noise F T B hB hBmeas hnull ell g (fun i => (hLip i).continuous) K hK N) Y) t ≤
      (2 * (T : ℝ) * (Lb : ℝ) ^ 2 +
        8 * (∑ i, ‖ell i‖ * (L i : ℝ)) ^ 2) *
          ∫ s, runningProfile F T X Y s ∂timeMeasure_T t := by
  let D := drift F T hnull b hb C hC hbC
  let J := noise F T B hB hBmeas hnull ell g (fun i => (hLip i).continuous) K hK N
  have hd := drift_local_sq_le F T t ht hnull b hb C hC hbC X Y
  have hj := noise_local_sq_le F T B hB hBmeas hnull ell g L hLip K hK t ht N hN X Y
  have heq : (StrongSDE.picardStep X₀ D J X).val -
      (StrongSDE.picardStep X₀ D J Y).val =
        ((D X).val - (D Y).val) + ((J X).val - (J Y).val) := by
    change (X₀.val + (D X).val + (J X).val) -
      (X₀.val + (D Y).val + (J Y).val) = _
    abel
  change ‖vectorStopPathLp T t
    ((StrongSDE.picardStep X₀ D J X).val - (StrongSDE.picardStep X₀ D J Y).val)‖ ^ 2 ≤ _
  rw [heq, map_add]
  have h := StrongSDE.norm_add_sq_le
    (vectorStopPathLp T t ((D X).val - (D Y).val))
    (vectorStopPathLp T t ((J X).val - (J Y).val))
  change ‖vectorStopPathLp T t ((D X).val - (D Y).val)‖ ^ 2 ≤ _ at hd
  change ‖vectorStopPathLp T t ((J X).val - (J Y).val)‖ ^ 2 ≤ _ at hj
  nlinarith

/-- Global-in-horizon Picard existence and uniqueness. The fixed-point engine
uses a sufficiently high factorial iterate; no short-window assumption occurs. -/
theorem exists_unique_concrete_picard_global {ι : Type*} [Fintype ι]
    (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (B : ι → ℝ≥0 → Ω → ℝ) [∀ i, IsFilteredPreBrownian (B i) F μ]
    (hB : ∀ i ω, Continuous (fun s => B i s ω))
    (hBmeas : ∀ i s, Measurable (B i s))
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (ell : ι → E) (g : ι → E → ℝ) (L : ι → ℝ≥0)
    (hLip : ∀ i, LipschitzWith (L i) (g i)) (K : ι → ℝ)
    (hK : ∀ i x, |g i x| ≤ K i)
    (b : E → E) (Lb : ℝ≥0) (hb : LipschitzWith Lb b)
    (C : ℝ) (hC : 0 ≤ C) (hbC : ∀ x, ‖b x‖ ≤ C)
    (X₀ : State (E := E) (μ := μ) F T) (N : ℕ) (hN : 1 ≤ N) :
    ∃! X : State (E := E) (μ := μ) F T,
      StrongSDE.picardStep X₀ (drift F T hnull b hb C hC hbC)
        (noise F T B hB hBmeas hnull ell g (fun i => (hLip i).continuous) K hK N) X = X := by
  apply exists_unique_of_runningProfile_volterra F T _
    (K := 2 * (T : ℝ) * (Lb : ℝ) ^ 2 + 8 * (∑ i, ‖ell i‖ * (L i : ℝ)) ^ 2)
    (by positivity)
  intro X Y t ht
  exact picardStep_local_sq_le F T t ht B hB hBmeas hnull ell g L hLip K hK
    b Lb hb C hC hbC X₀ N hN X Y

end Ripple.Stochastic.StrongSDETimeEstimate
