import Ripple.Stochastic.ContinuousItoStoppedIsometry
import Ripple.Stochastic.ContinuousItoStoppedMartingale
import Ripple.Stochastic.ContinuousItoHalfLineStopping
import Ripple.Stochastic.ClockInverseStopping
import Ripple.Stochastic.KnightStoppedClock

/-!
# Second moments at inverse-clock stops

The random stopping identity and increment isometry are instantiated for the
actual continuous Itô integral. The only clock identification input is the
ordinary pathwise time integral of the squared raw integrand.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Ripple.Stochastic.ClockStoppedIntegral
open Ripple.Analysis Ripple.ProbabilityTheory
open FilteredItoIntegralL2 FilteredItoIntegralCLM FilteredItoIntegralProcessGeneral
open AdaptedContinuousSpace ContinuousItoElementary ContinuousItoConsistency
open ContinuousItoStoppingGrid ContinuousItoStopping ContinuousItoStoppedMartingale
open ContinuousItoStoppedIsometry

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
  [IsFilteredPreBrownian B F μ]

/-- Conversion between the installed WithTop inverse time and the earlier
ENNReal inverse-clock path evaluator. In particular, infinity does not become zero. -/
theorem cappedStopTime_clockInverseTime (T : ℝ≥0)
    (A : ℝ≥0 → Ω → ℝ≥0) (u : ℝ≥0) (ω : Ω) :
    cappedStopTime T (clockInverseTime A u) ω =
      clockStoppedTime (fun t => A t ω) u T := by
  apply WithTop.coe_injective
  rw [coe_cappedStopTime]
  by_cases h : clockInverse (fun t => A t ω) u = ⊤
  · simp [clockInverseTime, clockStoppedTime, h]
  · simp [clockInverseTime, clockStoppedTime, h, min_comm]

/-- Increment isometry for the actual stopped continuous path, including
extended stopping times. Both energy endpoints are finite minima, so an
infinite stop preserves the original deterministic interval. -/
theorem stoppedContinuousIto_increment_raw_moment (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (H : ℝ≥0 × Ω → ℝ) (hHsm : StronglyMeasurable[F.predictable] H)
    (hH : MemLp H 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (s t : Set.Icc (0 : ℝ≥0) T) (hst : s ≤ t) :
    (∫ ω, (stoppedContinuousIto T hB hBmeas τ (hH.toLp H) t ω -
        stoppedContinuousIto T hB hBmeas τ (hH.toLp H) s ω) ^ 2 ∂μ) =
      ∫ ω, (∫ r in Set.Ioc (cappedStopTime s.val τ ω) (cappedStopTime t.val τ ω),
        H (r, ω) ^ 2 ∂timeMeasure) ∂μ := by
  have he := continuousIto_stopped_increment_raw_moment T hB hBmeas
    (cappedStopTime_isStoppingTime T hτ) (cappedStopTime_le T τ)
    H hHsm hH s t hst
  change (∫ ω, (stoppedContinuousIto T hB hBmeas τ (hH.toLp H) t ω -
        stoppedContinuousIto T hB hBmeas τ (hH.toLp H) s ω) ^ 2 ∂μ) = _ at he
  rw [he]
  apply integral_congr_ae
  filter_upwards with ω
  rw [ContinuousItoHalfLineStopping.cappedStopTime_min s.property.2 τ ω,
    ContinuousItoHalfLineStopping.cappedStopTime_min t.property.2 τ ω]

/-- Stopping the raw integrand restricts its time energy to the finite minimum.
This is a deterministic indicator identity, valid before imposing integrability. -/
theorem stoppedRaw_timeEnergy (H : ℝ≥0 × Ω → ℝ) (τ : Ω → WithTop ℝ≥0)
    (t : ℝ≥0) (ω : Ω) :
    (∫ r in Set.Ioc 0 t,
      (ContinuousItoHalfLineStopping.stoppedRawIntegrand τ H (r, ω)) ^ 2 ∂timeMeasure) =
      ∫ r in Set.Ioc 0 (cappedStopTime t τ ω), H (r, ω) ^ 2 ∂timeMeasure := by
  rw [← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with r
  have hcap : r ≤ cappedStopTime t τ ω ↔
      (r : WithTop ℝ≥0) ≤ τ ω ∧ r ≤ t := by
    rw [← WithTop.coe_le_coe, coe_cappedStopTime, le_min_iff, WithTop.coe_le_coe]
  by_cases hr : 0 < r <;> by_cases ht : r ≤ t <;>
    by_cases hs : (r : WithTop ℝ≥0) ≤ τ ω <;>
    simp [ContinuousItoHalfLineStopping.stoppedRawIntegrand,
      StoppedPredictableIntegrand.stoppingRegion, Set.indicator_apply, Set.mem_Ioc,
      hcap, hr, ht, hs]

/-- The cumulative stopped raw energy is the actual capped clock. -/
theorem clockStoppedRaw_energy (H : ℝ≥0 × Ω → ℝ)
    (A : ℝ≥0 → Ω → ℝ≥0)
    (hclock : ∀ ω r, (∫ v in Set.Ioc 0 r, H (v, ω) ^ 2 ∂timeMeasure) = (A r ω : ℝ))
    (u t : ℝ≥0) (ω : Ω) :
    (∫ r in Set.Ioc 0 t,
      (ContinuousItoHalfLineStopping.stoppedRawIntegrand (clockInverseTime A u) H (r, ω)) ^ 2
        ∂timeMeasure) = (A (clockStoppedTime (fun r => A r ω) u t) ω : ℝ) := by
  rw [stoppedRaw_timeEnergy, hclock, cappedStopTime_clockInverseTime]

/-- The stopped raw integrand has pathwise cumulative energy bounded by the clock cap. -/
theorem clockStoppedRaw_energy_le (H : ℝ≥0 × Ω → ℝ)
    (A : ℝ≥0 → Ω → ℝ≥0)
    (hc : ∀ ω, Continuous (fun t => A t ω)) (hm : ∀ ω, Monotone (fun t => A t ω))
    (hz : ∀ ω, A 0 ω = 0)
    (hclock : ∀ ω r, (∫ v in Set.Ioc 0 r, H (v, ω) ^ 2 ∂timeMeasure) = (A r ω : ℝ))
    (u t : ℝ≥0) (ω : Ω) :
    (∫ r in Set.Ioc 0 t,
      (ContinuousItoHalfLineStopping.stoppedRawIntegrand (clockInverseTime A u) H (r, ω)) ^ 2
        ∂timeMeasure) ≤ (u : ℝ) := by
  rw [clockStoppedRaw_energy H A hclock]
  exact_mod_cast clock_at_stoppedTime_le (hc ω) (hm ω) (hz ω) u t

/-- The general integral starts at zero, deduced from its installed time-indexed isometry. -/
theorem itoProcessCLM_zero (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    itoProcessCLM (𝓖 := F) (μ := μ) T 0 hBmeas φ = 0 := by
  have h := itoProcessCLM_norm_sq (𝓖 := F) (μ := μ) (t := 0) zero_le hBmeas φ
  have hz : ‖itoProcessCLM (𝓖 := F) (μ := μ) T 0 hBmeas φ‖ ^ 2 = 0 := by simpa using h
  exact norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp hz)

/-- Zero initial value for the selected continuous representative. -/
theorem continuousIto_zero_ae (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    (fun ω => representative (continuousIto T hB hBmeas φ) ω
      (⟨0, zero_le, zero_le⟩ : Set.Icc (0 : ℝ≥0) T)) =ᵐ[μ] 0 := by
  have he := representative_eval_ae T hB hBmeas φ ⟨0, zero_le, zero_le⟩
  rw [itoProcessCLM_zero T hBmeas φ] at he
  exact he.trans (Lp.coeFn_zero ℝ 2 μ)

/-- A real second-moment bound gives the same extended nonnegative moment bound. -/
theorem lintegral_sq_le_of_integral_sq_le {X : Ω → ℝ} (hX : MemLp X 2 μ)
    {C : ℝ≥0} (hbound : (∫ ω, X ω ^ 2 ∂μ) ≤ (C : ℝ)) :
    (∫⁻ ω, (‖X ω‖₊ : ℝ≥0∞) ^ 2 ∂μ) ≤ C := by
  have he := ofReal_integral_eq_lintegral_ofReal hX.integrable_sq
    (ae_of_all μ fun ω => sq_nonneg (X ω))
  have hpoint : (fun ω => ENNReal.ofReal (X ω ^ 2)) =
      fun ω => (‖X ω‖₊ : ℝ≥0∞) ^ 2 := by
    funext ω
    have hx : X ω ^ 2 = ((‖X ω‖₊ ^ 2 : ℝ≥0) : ℝ) := by
      simp [sq_abs]
    rw [hx, ENNReal.ofReal_coe_nnreal, ENNReal.coe_pow]
  rw [hpoint] at he
  rw [← he]
  simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hbound

/-- The actual inverse-clock-stopped integral has second moment at most the
clock level, at every time in the finite window. No stochastic stopping or
isometry law is an input. -/
theorem clockStoppedContinuousIto_secondMoment_le (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    [F.IsRightContinuous] (A : ℝ≥0 → Ω → ℝ≥0)
    (ha : Adapted F A) (hc : ∀ ω, Continuous (fun t => A t ω))
    (hm : ∀ ω, Monotone (fun t => A t ω)) (hz : ∀ ω, A 0 ω = 0)
    (H : ℝ≥0 × Ω → ℝ) (hHsm : StronglyMeasurable[F.predictable] H)
    (hH : MemLp H 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (hclock : ∀ ω r, (∫ v in Set.Ioc 0 r, H (v, ω) ^ 2 ∂timeMeasure) = (A r ω : ℝ))
    (u : ℝ≥0) (t : Set.Icc (0 : ℝ≥0) T) :
    (∫⁻ ω, (‖stoppedContinuousIto T hB hBmeas (clockInverseTime A u)
      (hH.toLp H) t ω‖₊ : ℝ≥0∞) ^ 2 ∂μ) ≤ u := by
  let τ := clockInverseTime A u
  have hτ := clockInverseTime_isStoppingTime ha hc hm hz u
  let σ := cappedStopTime T τ
  have hσ := cappedStopTime_isStoppingTime T hτ
  have hiso := continuousIto_stopped_increment_raw_moment T hB hBmeas hσ
    (cappedStopTime_le T τ) H hHsm hH ⟨0, zero_le, zero_le⟩ t t.property.1
  have hmoment : (∫ ω, (stoppedContinuousIto T hB hBmeas τ (hH.toLp H) t ω) ^ 2 ∂μ) =
      ∫ ω, (A (clockStoppedTime (fun r => A r ω) u t.val) ω : ℝ) ∂μ := by
    calc
      _ = ∫ ω, (representative (continuousIto T hB hBmeas (hH.toLp H)) ω
          (stoppedWindowTime T σ ω t) -
        representative (continuousIto T hB hBmeas (hH.toLp H)) ω
          (stoppedWindowTime T σ ω ⟨0, zero_le, zero_le⟩)) ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [continuousIto_zero_ae T hB hBmeas (hH.toLp H)] with ω hω
        have hzero : representative (continuousIto T hB hBmeas (hH.toLp H)) ω
            (stoppedWindowTime T σ ω ⟨0, zero_le, zero_le⟩) = 0 := by
          simpa only [stoppedWindowTime, min_eq_left zero_le, Pi.zero_apply] using hω
        rw [hzero, sub_zero]
        rfl
      _ = _ := by
        rw [hiso]
        apply integral_congr_ae
        filter_upwards with ω
        simp only [min_eq_left zero_le]
        rw [hclock]
        congr 2
        exact (ContinuousItoHalfLineStopping.cappedStopTime_min t.property.2 τ ω).trans
          (cappedStopTime_clockInverseTime t.val A u ω)
  apply lintegral_sq_le_of_integral_sq_le
    (stoppedContinuousIto_memLp T hB hBmeas hτ (hH.toLp H) t)
  rw [hmoment]
  have hcap : ∀ ω, (A (clockStoppedTime (fun r => A r ω) u t.val) ω : ℝ) ≤ (u : ℝ) :=
    fun ω => by exact_mod_cast clock_at_stoppedTime_le (hc ω) (hm ω) (hz ω) u t.val
  by_cases hint : Integrable (fun ω => (A (clockStoppedTime (fun r => A r ω) u t.val) ω : ℝ)) μ
  · calc
      _ ≤ ∫ _ : Ω, (u : ℝ) ∂μ := integral_mono hint (integrable_const _) hcap
      _ = (u : ℝ) := by simp
  · rw [integral_undef hint]
    exact u.coe_nonneg

end Ripple.Stochastic.ClockStoppedIntegral
