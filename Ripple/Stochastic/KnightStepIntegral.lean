import Ripple.Stochastic.KnightStepCoefficients
import Ripple.Stochastic.ClockStoppedIntegral
import Ripple.Stochastic.ContinuousItoLinear
import Ripple.Stochastic.ContinuousAdaptedIntegrand

/-!
# The actual integrands of a rectangular inverse-clock grid

The masks are half open in clock time. They need not be continuous in physical
time. Strict-past sampling nevertheless converges at every time because clocks
are continuous and nondecreasing. This supplies a common deterministic-grid
approximation without a continuity premise on the masked integrand.

Stops are extended times and are capped before finite
evaluation; the formulas therefore include finite terminal clocks.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Ripple.Stochastic.Knight
open Ripple.Analysis Ripple.ProbabilityTheory
open AdaptedContinuousSpace ContinuousItoElementary ContinuousItoLinear
open FilteredItoIntegralL2 FilteredItoIntegralCLM
open StoppedPredictableIntegrand ContinuousItoStopping
open ContinuousItoHalfLineStopping ContinuousAdaptedIntegrand ContinuousItoStoppingGrid

variable {ι κ Ω : Type*} [Fintype κ]

/-- The channelwise physical-time integrand for a rectangular clock grid. -/
def stepIntegrand (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (H : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0)
    (i : ι) (t : ℝ≥0) (ω : Ω) : ℝ :=
  channelCoefficient g θ i (A i t ω) * H i t ω

/-- Safe counterpart of `stepSum`, also meaningful above a finite terminal clock. -/
def cappedStepSum (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (M : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ j, θ j *
    (M (g.channel j) (clockStoppedTime (fun s => A (g.channel j) s ω) (g.upper j) t) ω -
      M (g.channel j) (clockStoppedTime (fun s => A (g.channel j) s ω) (g.lower j) t) ω)

/-- Below every terminal clock the safe and original formulas agree. -/
theorem cappedStepSum_eq_stepSum (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (M : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0)
    (ω : Ω) (hfinite : ∀ j,
      clockInverse (fun t => A (g.channel j) t ω) (g.upper j) ≠ ⊤)
    (t : ℝ≥0) : cappedStepSum g θ M A t ω = stepSum g θ M A t ω := by
  apply Finset.sum_congr rfl
  intro j _
  have hl : clockInverse (fun t => A (g.channel j) t ω) (g.lower j) ≠ ⊤ :=
    ne_top_of_le_ne_top (hfinite j)
      (clockInverse_mono (fun t => A (g.channel j) t ω) (g.ordered j))
  simp only [clockStoppedTime, if_neg (hfinite j), if_neg hl, inverseTime]

/-- The half-open clock mask converges under strict-past deterministic sampling.
At its lower endpoint it stays zero; at its upper endpoint it stays one. -/
theorem clockWindow_sample_tendsto (A : ℝ≥0 → ℝ≥0) (hc : Continuous A)
    (hm : Monotone A) (l u t : ℝ≥0) :
    Tendsto (fun n : ℕ => if l < A (leftGrid (1 / ((n : ℝ≥0) + 1)) t) ∧
      A (leftGrid (1 / ((n : ℝ≥0) + 1)) t) ≤ u then (1 : ℝ) else 0)
      atTop (nhds (if l < A t ∧ A t ≤ u then (1 : ℝ) else 0)) := by
  have ha := hc.continuousAt.tendsto.comp (tendsto_leftGrid t)
  have hle : ∀ n : ℕ, A (leftGrid (1 / ((n : ℝ≥0) + 1)) t) ≤ A t :=
    fun n => hm (leftGrid_le (by positivity) t)
  by_cases hl : l < A t
  · by_cases hu : A t ≤ u
    · have hev := ha.eventually (lt_mem_nhds hl)
      apply tendsto_const_nhds.congr'
      filter_upwards [hev] with n hn
      have hn' : l < A (leftGrid (1 / ((n : ℝ≥0) + 1)) t) := hn
      rw [if_pos ⟨hl, hu⟩, if_pos ⟨hn', (hle n).trans hu⟩]
    · have hev := ha.eventually (lt_mem_nhds (lt_of_not_ge hu))
      apply tendsto_const_nhds.congr'
      filter_upwards [hev] with n hn
      have hn' : u < A (leftGrid (1 / ((n : ℝ≥0) + 1)) t) := hn
      rw [if_neg (fun h => hu h.2), if_neg (fun h => absurd h.2 (not_le.mpr hn'))]
  · have hall : ∀ n : ℕ, ¬ l < A (leftGrid (1 / ((n : ℝ≥0) + 1)) t) :=
      fun n => not_lt_of_ge ((hle n).trans (le_of_not_gt hl))
    simpa only [hl, false_and, if_false, hall] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

theorem channelCoefficient_sample_tendsto (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (A : ℝ≥0 → ℝ≥0) (hc : Continuous A) (hm : Monotone A) (i : ι) (t : ℝ≥0) :
    Tendsto (fun n : ℕ => channelCoefficient g θ i
      (A (leftGrid (1 / ((n : ℝ≥0) + 1)) t))) atTop
      (nhds (channelCoefficient g θ i (A t))) := by
  classical
  apply tendsto_finset_sum
  intro j _
  by_cases hj : g.channel j = i
  · have h := (clockWindow_sample_tendsto A hc hm (g.lower j) (g.upper j) t).const_mul (θ j)
    simpa only [windowCoefficient, IntervalGrid.Active, hj, true_and,
      mul_ite, mul_one, mul_zero] using h
  · simpa only [windowCoefficient, IntervalGrid.Active, hj, false_and, if_false] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

/-- All channels and all windows use the identical physical-time grid. -/
theorem stepIntegrand_sample_tendsto (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (H : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0)
    (hH : ∀ i ω, Continuous (fun t => H i t ω))
    (hc : ∀ i ω, Continuous (fun t => A i t ω))
    (hm : ∀ i ω, Monotone (fun t => A i t ω)) (i : ι) (t : ℝ≥0) (ω : Ω) :
    Tendsto (fun n : ℕ => stepIntegrand g θ H A i
      (leftGrid (1 / ((n : ℝ≥0) + 1)) t) ω) atTop
      (nhds (stepIntegrand g θ H A i t ω)) :=
  (channelCoefficient_sample_tendsto g θ (fun t => A i t ω) (hc i ω) (hm i ω) i t).mul
    (((hH i ω).tendsto t).comp (tendsto_leftGrid t))

theorem stepIntegrand_bound (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (H : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ i t ω, |H i t ω| ≤ K)
    (i : ι) (t : ℝ≥0) (ω : Ω) :
    |stepIntegrand g θ H A i t ω| ≤ (∑ j, |θ j|) * K := by
  rw [stepIntegrand, abs_mul]
  exact mul_le_mul (abs_channelCoefficient_le g θ i (A i t ω)) (hb i t ω)
    (abs_nonneg _) (Finset.sum_nonneg fun j _ => abs_nonneg (θ j))

variable [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 mΩ}

/-- A path-level agreement on a deterministic window transfers through every
random clock stop in that window. This is the interface to the installed
integer-window/half-line consistency theorem. -/
theorem cappedStepSum_congr_ae_on (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (M N : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0) (T : ℝ≥0)
    (hMN : ∀ᵐ ω ∂μ, ∀ i s, s ≤ T → M i s ω = N i s ω) :
    ∀ᵐ ω ∂μ, ∀ t, t ≤ T → cappedStepSum g θ M A t ω = cappedStepSum g θ N A t ω := by
  filter_upwards [hMN] with ω hω t ht
  apply Finset.sum_congr rfl
  intro j _
  have hcap (i : ι) (u : ℝ≥0) : clockStoppedTime (fun r => A i r ω) u t ≤ T := by
    unfold clockStoppedTime
    split_ifs
    · exact ht
    · exact (min_le_left _ _).trans ht
  rw [hω _ _ (hcap _ _), hω _ _ (hcap _ _)]

theorem stepIntegrand_measurable (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (H : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0)
    (hH : ∀ i t, Measurable[F t] (H i t)) (ha : ∀ i, Adapted F (A i))
    (i : ι) (t : ℝ≥0) : Measurable[F t] (stepIntegrand g θ H A i t) := by
  classical
  change Measurable[F t] (fun ω =>
    (∑ j, windowCoefficient g θ i (A i t ω) j) * H i t ω)
  apply Measurable.mul _ (hH i t)
  apply Finset.measurable_fun_sum
  intro j _
  by_cases hj : g.channel j = i
  · simp only [windowCoefficient, IntervalGrid.Active, hj, true_and]
    exact measurable_const.ite
      ((measurableSet_lt measurable_const (ha i t)).inter
        (measurableSet_le (f := fun ω => A i t ω) (g := fun _ => g.upper j) (ha i t)
          measurable_const)) measurable_const
  · simpa only [windowCoefficient, IntervalGrid.Active, hj, false_and, if_false]
      using (measurable_const : Measurable[F t] (fun _ : Ω => (0 : ℝ)))

/-- Predictability follows from actual sampled adapted functions, rather than
from a continuity assertion about the masks. -/
theorem stepIntegrand_stronglyMeasurable (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (H : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0)
    (hHa : ∀ i t, Measurable[F t] (H i t)) (ha : ∀ i, Adapted F (A i))
    (hHc : ∀ i ω, Continuous (fun t => H i t ω))
    (hc : ∀ i ω, Continuous (fun t => A i t ω))
    (hm : ∀ i ω, Monotone (fun t => A i t ω)) (i : ι) :
    StronglyMeasurable[F.predictable] (Function.uncurry (stepIntegrand g θ H A i)) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply stronglyMeasurable_of_tendsto atTop
    (fun n : ℕ => (measurable_sample (stepIntegrand_measurable g θ H A hHa ha i)
      (show 0 < (1 : ℝ≥0) / ((n : ℝ≥0) + 1) from by positivity)).stronglyMeasurable)
  apply tendsto_pi_nhds.mpr
  intro z
  exact stepIntegrand_sample_tendsto g θ H A hHc hc hm i z.1 z.2

section ScalarStopping
variable {B : ℝ≥0 → Ω → ℝ} [IsFilteredPreBrownian B F μ]

/-- The selected continuous integral commutes with subtraction at all times
on one event. This is a path-valued statement. -/
theorem continuousItoNN_sub (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBm : ∀ t, Measurable (B t))
    (φ ψ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBm)) :
    ∀ᵐ ω ∂μ, ∀ t, continuousItoNN T hB hBm (φ - ψ) t ω =
      continuousItoNN T hB hBm φ t ω - continuousItoNN T hB hBm ψ t ω := by
  filter_upwards [continuousItoNN_add T hB hBm φ ((-1 : ℝ) • ψ),
    continuousItoNN_smul T hB hBm (-1) ψ] with ω ha hs t
  simpa only [neg_one_smul, sub_eq_add_neg, neg_mul, one_mul] using
    (ha t).trans (congrArg (fun x => continuousItoNN T hB hBm φ t ω + x) (hs t))

/-- One inverse-clock window is the integral of the difference of its two
stochastic-interval restrictions. No window-integral identity is assumed. -/
theorem continuousItoNN_clockWindow (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBm : ∀ t, Measurable (B t))
    (A : ℝ≥0 → Ω → ℝ≥0) (l u : ℝ≥0)
    (hl : IsStoppingTime F (clockInverseTime A l))
    (hu : IsStoppingTime F (clockInverseTime A u))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBm)) :
    ∀ᵐ ω ∂μ, ∀ t : Set.Icc (0 : ℝ≥0) T,
      continuousItoNN T hB hBm
          (stoppedIntegrand T hBm hu φ - stoppedIntegrand T hBm hl φ) t.val ω =
        continuousItoNN T hB hBm φ
          (clockStoppedTime (fun r => A r ω) u t.val) ω -
        continuousItoNN T hB hBm φ
          (clockStoppedTime (fun r => A r ω) l t.val) ω := by
  filter_upwards [continuousItoNN_sub T hB hBm
      (stoppedIntegrand T hBm hu φ) (stoppedIntegrand T hBm hl φ),
    continuousIto_stopped T hB hBm hu φ, continuousIto_stopped T hB hBm hl φ]
      with ω hsub hupper hlower t
  rw [hsub]
  have htime (v : ℝ≥0) :
      (stoppedWindowTime T (cappedStopTime T (clockInverseTime A v)) ω t).val =
        clockStoppedTime (fun r => A r ω) v t.val :=
    (cappedStopTime_min t.property.2 (clockInverseTime A v) ω).trans
      (ClockStoppedIntegral.cappedStopTime_clockInverseTime t.val A v ω)
  have hle (v : ℝ≥0) : clockStoppedTime (fun r => A r ω) v t.val ≤ T := by
    rw [← htime v]
    exact (stoppedWindowTime T (cappedStopTime T (clockInverseTime A v)) ω t).property.2
  have hpoint (v : ℝ≥0) :
      stoppedWindowTime T (cappedStopTime T (clockInverseTime A v)) ω t =
        (⟨clockStoppedTime (fun r => A r ω) v t.val, zero_le, hle v⟩ : Icc (0 : ℝ≥0) T) :=
    Subtype.ext (htime v)
  have hup := hupper t
  have hlo := hlower t
  rw [hpoint u] at hup
  rw [hpoint l] at hlo
  simpa only [continuousItoNN, min_eq_left t.property.2, min_eq_left (hle u),
    min_eq_left (hle l)] using congrArg₂ (· - ·) hup hlo

end ScalarStopping

/-- The raw stochastic-interval difference for one clock window. -/
def windowIntegrand (A : ℝ≥0 → Ω → ℝ≥0) (H : ℝ≥0 → Ω → ℝ)
    (l u : ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ :=
  stoppedRawIntegrand (clockInverseTime A u) (Function.uncurry H) (t, ω) -
    stoppedRawIntegrand (clockInverseTime A l) (Function.uncurry H) (t, ω)

/-- The stopped raw integrand at an inverse-clock time is the clock-level mask. -/
theorem stoppedRaw_clock_apply (A : ℝ≥0 → Ω → ℝ≥0) (H : ℝ≥0 × Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => A t ω))
    (hm : ∀ ω, Monotone (fun t => A t ω)) (hz : ∀ ω, A 0 ω = 0)
    (v t : ℝ≥0) (ω : Ω) :
    stoppedRawIntegrand (clockInverseTime A v) H (t, ω) =
      if 0 < t ∧ A t ω ≤ v then H (t, ω) else 0 := by
  classical
  have he : (t : WithTop ℝ≥0) ≤ clockInverseTime A v ω ↔ A t ω ≤ v := by
    simpa only [not_lt] using not_congr (clockInverseTime_lt_iff hc hm hz v t ω)
  unfold stoppedRawIntegrand
  by_cases h : 0 < t ∧ A t ω ≤ v
  · have hmem : (t, ω) ∈ stoppingRegion (clockInverseTime A v) := ⟨h.1, he.2 h.2⟩
    rw [Set.indicator_of_mem hmem, if_pos h]
  · have hmem : (t, ω) ∉ stoppingRegion (clockInverseTime A v) := fun hh =>
      h ⟨hh.1, he.1 hh.2⟩
    rw [Set.indicator_of_notMem hmem, if_neg h]

/-- Inverse-clock stopping produces exactly the half-open clock window. -/
theorem windowIntegrand_eq (A : ℝ≥0 → Ω → ℝ≥0) (H : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => A t ω))
    (hm : ∀ ω, Monotone (fun t => A t ω)) (hz : ∀ ω, A 0 ω = 0)
    {l u : ℝ≥0} (hlu : l ≤ u) (t : ℝ≥0) (ω : Ω) :
    windowIntegrand A H l u t ω = if l < A t ω ∧ A t ω ≤ u then H t ω else 0 := by
  classical
  unfold windowIntegrand
  rw [stoppedRaw_clock_apply A _ hc hm hz u t ω, stoppedRaw_clock_apply A _ hc hm hz l t ω]
  by_cases ht : 0 < t
  · by_cases hl : l < A t ω
    · by_cases hu : A t ω ≤ u
      · rw [if_pos ⟨ht, hu⟩, if_neg (fun h => absurd h.2 (not_le.mpr hl)), if_pos ⟨hl, hu⟩]
        simp [Function.uncurry]
      · rw [if_neg (fun h => hu h.2), if_neg (fun h => absurd h.2 (not_le.mpr hl)),
          if_neg (fun h => hu h.2)]
        simp
    · have hAl : A t ω ≤ l := le_of_not_gt hl
      have hAu : A t ω ≤ u := hAl.trans hlu
      rw [if_pos ⟨ht, hAu⟩, if_pos ⟨ht, hAl⟩, if_neg (fun h => hl h.1)]
      simp
  · have htz : t = 0 := le_antisymm (le_of_not_gt ht) bot_le
    subst htz
    rw [if_neg (fun h => ht h.1), if_neg (fun h => ht h.1),
      if_neg (fun h => absurd h.1 (by simp [hz]))]
    simp

section RawIntegralLinearity
variable {B : ℝ≥0 → Ω → ℝ} [IsFilteredPreBrownian B F μ]

theorem stoppedRaw_toLp (T : ℝ≥0) (hBm : ∀ t, Measurable (B t))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (H : ℝ≥0 × Ω → ℝ)
    (hH : MemLp H 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBm)) :
    (memLp_stopped hτ hH).toLp _ = stoppedIntegrand T hBm hτ (hH.toLp H) := by
  apply Lp.ext
  filter_upwards [(memLp_stopped hτ hH).coeFn_toLp,
    stoppedIntegrand_coeFn T hBm hτ (hH.toLp H), hH.coeFn_toLp] with z hs ht hraw
  refine hs.trans (Eq.trans ?_ ht.symm)
  by_cases hz : z ∈ stoppingRegion τ
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, hraw]
  · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]

theorem windowIntegrand_memLp (T : ℝ≥0) (hBm : ∀ t, Measurable (B t))
    (A : ℝ≥0 → Ω → ℝ≥0) (H : ℝ≥0 → Ω → ℝ) (l u : ℝ≥0)
    (hl : IsStoppingTime F (clockInverseTime A l))
    (hu : IsStoppingTime F (clockInverseTime A u))
    (hH : MemLp (Function.uncurry H) 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBm)) :
    MemLp (Function.uncurry (windowIntegrand A H l u)) 2
      (trimMeasure_T (𝓖 := F) (μ := μ) T hBm) :=
  (memLp_stopped hu hH).sub (memLp_stopped hl hH)

/-- One raw clock window is identified with the actual original integral
evaluated at its two safe inverse-clock stops, simultaneously at all times. -/
theorem continuousItoOfFun_window (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBm : ∀ t, Measurable (B t))
    (A : ℝ≥0 → Ω → ℝ≥0) (H : ℝ≥0 → Ω → ℝ) (l u : ℝ≥0)
    (hl : IsStoppingTime F (clockInverseTime A l))
    (hu : IsStoppingTime F (clockInverseTime A u))
    (hH : MemLp (Function.uncurry H) 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBm)) :
    ∀ᵐ ω ∂μ, ∀ t : Icc (0 : ℝ≥0) T,
      continuousItoOfFun μ F T hB hBm (windowIntegrand A H l u) t.val ω =
        continuousItoOfFun μ F T hB hBm H
          (clockStoppedTime (fun r => A r ω) u t.val) ω -
        continuousItoOfFun μ F T hB hBm H
          (clockStoppedTime (fun r => A r ω) l t.val) ω := by
  have hw := windowIntegrand_memLp T hBm A H l u hl hu hH
  have hclass : hw.toLp _ = stoppedIntegrand T hBm hu (hH.toLp _) -
      stoppedIntegrand T hBm hl (hH.toLp _) := by
    rw [show hw.toLp _ = (memLp_stopped hu hH).toLp _ -
        (memLp_stopped hl hH).toLp _ from MemLp.toLp_sub _ _,
      stoppedRaw_toLp (B := B) T hBm hu _ hH, stoppedRaw_toLp (B := B) T hBm hl _ hH]
    rfl
  rw [continuousItoOfFun_of_memLp T hB hBm hw,
    continuousItoOfFun_of_memLp T hB hBm hH, hclass]
  exact continuousItoNN_clockWindow T hB hBm A l u hl hu (hH.toLp _)

theorem finsetSum_memLp (T : ℝ≥0) (hBm : ∀ t, Measurable (B t)) (S : Finset κ)
    (G : κ → ℝ≥0 → Ω → ℝ)
    (hG : ∀ j, MemLp (Function.uncurry (G j)) 2
      (trimMeasure_T (𝓖 := F) (μ := μ) T hBm)) :
    MemLp (Function.uncurry fun t ω => ∑ j ∈ S, G j t ω) 2
      (trimMeasure_T (𝓖 := F) (μ := μ) T hBm) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using MemLp.zero
  | @insert j S hj ih =>
      simpa only [Finset.sum_insert hj] using (hG j).add ih

/-- Raw-function finite additivity, with L² membership constructed from the
actual summands. -/
theorem continuousItoOfFun_finset_sum (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBm : ∀ t, Measurable (B t))
    (S : Finset κ) (G : κ → ℝ≥0 → Ω → ℝ)
    (hG : ∀ j, MemLp (Function.uncurry (G j)) 2
      (trimMeasure_T (𝓖 := F) (μ := μ) T hBm)) :
    ∀ᵐ ω ∂μ, ∀ t,
      continuousItoOfFun μ F T hB hBm (fun r ω => ∑ j ∈ S, G j r ω) t ω =
        ∑ j ∈ S, continuousItoOfFun μ F T hB hBm (G j) t ω := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      have hz : MemLp (Function.uncurry fun (_ : ℝ≥0) (_ : Ω) => (0 : ℝ)) 2
          (trimMeasure_T (𝓖 := F) (μ := μ) T hBm) := MemLp.zero
      have he := continuousItoOfFun_const_mul T hB hBm hz (0 : ℝ)
      simpa only [Finset.sum_empty, zero_mul] using he
  | @insert j S hj ih =>
      filter_upwards [ih, continuousItoOfFun_add T hB hBm (hG j)
        (finsetSum_memLp T hBm S G hG)] with ω hi ha t
      simp only [Finset.sum_insert hj]
      rw [ha, hi]

open Classical in
/-- Within one Brownian channel, integration of the clock coefficient gives
the sum of its actual stopped increments. -/
theorem continuousItoOfFun_stepIntegrand (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (T : ℝ≥0) (hB : ∀ ω, Continuous (fun t => B t ω)) (hBm : ∀ t, Measurable (B t))
    (H : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0) (i : ι)
    (hc : ∀ ω, Continuous (fun t => A i t ω))
    (hm : ∀ ω, Monotone (fun t => A i t ω)) (hz : ∀ ω, A i 0 ω = 0)
    (hstop : ∀ u, IsStoppingTime F (clockInverseTime (A i) u))
    (hH : MemLp (Function.uncurry (H i)) 2
      (trimMeasure_T (𝓖 := F) (μ := μ) T hBm)) :
    ∀ᵐ ω ∂μ, ∀ t : Icc (0 : ℝ≥0) T,
      continuousItoOfFun μ F T hB hBm (stepIntegrand g θ H A i) t.val ω =
        ∑ j, if g.channel j = i then θ j *
          (continuousItoOfFun μ F T hB hBm (H i)
              (clockStoppedTime (fun r => A i r ω) (g.upper j) t.val) ω -
            continuousItoOfFun μ F T hB hBm (H i)
              (clockStoppedTime (fun r => A i r ω) (g.lower j) t.val) ω) else 0 := by
  classical
  let G := fun j t ω => if g.channel j = i then
    θ j * windowIntegrand (A i) (H i) (g.lower j) (g.upper j) t ω else 0
  have hG : ∀ j, MemLp (Function.uncurry (G j)) 2
      (trimMeasure_T (𝓖 := F) (μ := μ) T hBm) := by
    intro j
    by_cases hj : g.channel j = i
    · simpa only [G, hj, if_true] using
        (windowIntegrand_memLp T hBm (A i) (H i) _ _ (hstop _) (hstop _) hH).const_mul (θ j)
    · simpa only [G, hj, if_false] using
        (MemLp.zero : MemLp (fun _ : ℝ≥0 × Ω => (0 : ℝ)) 2
          (trimMeasure_T (𝓖 := F) (μ := μ) T hBm))
  have hexpand : stepIntegrand g θ H A i = fun t ω => ∑ j, G j t ω := by
    funext t ω
    rw [stepIntegrand, channelCoefficient, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [show G j t ω = if g.channel j = i then θ j *
      (if g.lower j < A i t ω ∧ A i t ω ≤ g.upper j then H i t ω else 0) else 0 by
        simp only [G, windowIntegrand_eq (A i) (H i) hc hm hz (g.ordered j)]]
    by_cases hj : g.channel j = i <;>
      by_cases hw : g.lower j < A i t ω ∧ A i t ω ≤ g.upper j <;>
      simp [windowCoefficient, IntervalGrid.Active, hj, hw]
  have heach : ∀ j, ∀ᵐ ω ∂μ, ∀ t : Icc (0 : ℝ≥0) T,
      continuousItoOfFun μ F T hB hBm (G j) t.val ω =
        if g.channel j = i then θ j *
          (continuousItoOfFun μ F T hB hBm (H i)
              (clockStoppedTime (fun r => A i r ω) (g.upper j) t.val) ω -
            continuousItoOfFun μ F T hB hBm (H i)
              (clockStoppedTime (fun r => A i r ω) (g.lower j) t.val) ω) else 0 := by
    intro j
    by_cases hj : g.channel j = i
    · filter_upwards [continuousItoOfFun_const_mul T hB hBm
          (windowIntegrand_memLp T hBm (A i) (H i) (g.lower j) (g.upper j) (hstop _) (hstop _) hH)
          (θ j),
        continuousItoOfFun_window T hB hBm (A i) (H i) (g.lower j) (g.upper j) (hstop _)
          (hstop _) hH]
          with ω hscale hwindow t
      simpa only [G, hj, if_true, hwindow t] using hscale t.val
    · have hzraw : MemLp (Function.uncurry fun (_ : ℝ≥0) (_ : Ω) => (0 : ℝ)) 2
          (trimMeasure_T (𝓖 := F) (μ := μ) T hBm) := MemLp.zero
      have hzero := continuousItoOfFun_const_mul T hB hBm hzraw (0 : ℝ)
      simpa only [G, hj, if_false, zero_mul] using hzero.mono (fun ω hω (t : Icc (0 : ℝ≥0) T) => hω t.val)
  filter_upwards [continuousItoOfFun_finset_sum T hB hBm Finset.univ G hG,
    ae_all_iff.mpr heach] with ω hsum hj t
  rw [hexpand, hsum]
  exact Finset.sum_congr rfl fun j _ => hj j t

end RawIntegralLinearity

/-- A stopped clock reads exactly `min (A t) u`, including when its inverse
is infinite. This is stronger than merely bounding the stopped clock. -/
theorem clock_at_stoppedTime_eq_min (A : ℝ≥0 → ℝ≥0)
    (hc : Continuous A) (hm : Monotone A) (hz : A 0 = 0) (u t : ℝ≥0) :
    A (clockStoppedTime A u t) = min (A t) u := by
  by_cases htu : A t ≤ u
  · rw [clockStoppedTime_eq_self_of_le ((le_clockInverse_iff hc hm hz u t).mpr htu),
      min_eq_left htu]
  · have hlt : (u : ℝ≥0∞) < terminalClock A :=
      (show (u : ℝ≥0∞) < (A t : ℝ≥0∞) from by exact_mod_cast lt_of_not_ge htu).trans_le
        (le_iSup (fun s : ℝ≥0 => (A s : ℝ≥0∞)) t)
    have hf := clockInverse_ne_top_of_lt_terminal hlt
    have hinv : clockInverse A u < (t : ℝ≥0∞) :=
      (clockInverse_lt_iff hc hm hz u t).mpr (lt_of_not_ge htu)
    have hfin : (clockInverse A u).toNNReal ≤ t := by
      rw [← ENNReal.coe_toNNReal hf] at hinv
      exact_mod_cast hinv.le
    rw [clockStoppedTime, if_neg hf, min_eq_right hfin, min_eq_right (le_of_not_ge htu)]
    exact clock_at_clockInverse hc hm hz hlt

/-- The squared clock-window mask is the difference of the two stopped
energies. This identity also handles zero-length windows. -/
theorem clockWindow_sq (A : ℝ≥0 → Ω → ℝ≥0) (H : ℝ≥0 × Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => A t ω))
    (hm : ∀ ω, Monotone (fun t => A t ω)) (hz : ∀ ω, A 0 ω = 0)
    {l u : ℝ≥0} (hlu : l ≤ u) (r : ℝ≥0) (ω : Ω) :
    (if l < A r ω ∧ A r ω ≤ u then H (r, ω) ^ 2 else 0) =
      (stoppedRawIntegrand (clockInverseTime A u) H (r, ω)) ^ 2 -
        (stoppedRawIntegrand (clockInverseTime A l) H (r, ω)) ^ 2 := by
  classical
  rw [stoppedRaw_clock_apply A H hc hm hz u r ω, stoppedRaw_clock_apply A H hc hm hz l r ω]
  by_cases hr : 0 < r
  · by_cases hl : l < A r ω
    · by_cases hu : A r ω ≤ u
      · rw [if_pos ⟨hl, hu⟩, if_pos ⟨hr, hu⟩, if_neg (fun h => absurd h.2 (not_le.mpr hl))]
        simp
      · rw [if_neg (fun h => hu h.2), if_neg (fun h => hu h.2),
          if_neg (fun h => absurd h.2 (not_le.mpr hl))]
        simp
    · have hAl : A r ω ≤ l := le_of_not_gt hl
      have hAu : A r ω ≤ u := hAl.trans hlu
      rw [if_neg (fun h => hl h.1), if_pos ⟨hr, hAu⟩, if_pos ⟨hr, hAl⟩]
      simp
  · have hrz : r = 0 := le_antisymm (le_of_not_gt hr) bot_le
    subst hrz
    rw [if_neg (fun h => absurd h.1 (by simp [hz])), if_neg (fun h => hr h.1),
      if_neg (fun h => hr h.1)]
    simp

/-- Exact time-integral energy of one half-open clock window. -/
theorem clockWindow_energy (A : ℝ≥0 → Ω → ℝ≥0) (H : ℝ≥0 × Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => A t ω))
    (hm : ∀ ω, Monotone (fun t => A t ω)) (hz : ∀ ω, A 0 ω = 0)
    (hclock : ∀ ω t, (∫ r in Ioc 0 t, H (r, ω) ^ 2 ∂timeMeasure) = (A t ω : ℝ))
    (henergy : ∀ ω t, IntegrableOn (fun r => H (r, ω) ^ 2) (Ioc 0 t) timeMeasure)
    {l u : ℝ≥0} (hlu : l ≤ u) (t : ℝ≥0) (ω : Ω) :
    (∫ r in Ioc 0 t, if l < A r ω ∧ A r ω ≤ u then H (r, ω) ^ 2 else 0 ∂timeMeasure) =
      (min (A t ω) u : ℝ) - (min (A t ω) l : ℝ) := by
  have hint (v : ℝ≥0) : IntegrableOn
      (fun r => (stoppedRawIntegrand (clockInverseTime A v) H (r, ω)) ^ 2)
      (Ioc 0 t) timeMeasure := by
    have heq : (fun r => (stoppedRawIntegrand (clockInverseTime A v) H (r, ω)) ^ 2) =
        (Ioi (0 : ℝ≥0) ∩ {r | A r ω ≤ v}).indicator
          (fun r => H (r, ω) ^ 2) := by
      funext r
      classical
      rw [stoppedRaw_clock_apply A H hc hm hz v r ω]
      by_cases h : 0 < r ∧ A r ω ≤ v
      · rw [if_pos h, Set.indicator_of_mem (show r ∈ Ioi (0 : ℝ≥0) ∩ {r | A r ω ≤ v} from
          ⟨h.1, h.2⟩)]
      · rw [if_neg h, Set.indicator_of_notMem (fun hh => h ⟨hh.1, hh.2⟩)]
        simp
    rw [heq]
    exact (henergy ω t).indicator
      (measurableSet_Ioi.inter (measurableSet_le (hc ω).measurable measurable_const))
  rw [show (fun r => if l < A r ω ∧ A r ω ≤ u then H (r, ω) ^ 2 else 0) =
      (fun r => (stoppedRawIntegrand (clockInverseTime A u) H (r, ω)) ^ 2 -
        (stoppedRawIntegrand (clockInverseTime A l) H (r, ω)) ^ 2) from
      funext fun r => clockWindow_sq A H hc hm hz hlu r ω,
    integral_sub (hint u) (hint l), ClockStoppedIntegral.stoppedRaw_timeEnergy,
    ClockStoppedIntegral.stoppedRaw_timeEnergy, hclock, hclock,
    ClockStoppedIntegral.cappedStopTime_clockInverseTime,
    ClockStoppedIntegral.cappedStopTime_clockInverseTime,
    clock_at_stoppedTime_eq_min _ (hc ω) (hm ω) (hz ω),
    clock_at_stoppedTime_eq_min _ (hc ω) (hm ω) (hz ω), NNReal.coe_min, NNReal.coe_min]

open Classical in
/-- Squaring the actual channel integrand removes precisely the off-diagonal
window terms, by separation within each channel. -/
theorem stepIntegrand_sq (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (H : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0)
    (i : ι) (t : ℝ≥0) (ω : Ω) :
    (stepIntegrand g θ H A i t ω) ^ 2 =
      ∑ j, if g.channel j = i ∧ g.lower j < A i t ω ∧ A i t ω ≤ g.upper j
        then θ j ^ 2 * (H i t ω) ^ 2 else 0 := by
  classical
  rw [stepIntegrand, mul_pow, channelCoefficient_sq_explicit, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

/-- The time-integral bracket of the masked finite-channel integral is
exactly the original `stepBracket`, rather than just bounded by it. -/
theorem stepIntegrand_energy [Fintype ι] (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (H : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0)
    (hc : ∀ i ω, Continuous (fun t => A i t ω))
    (hm : ∀ i ω, Monotone (fun t => A i t ω)) (hz : ∀ i ω, A i 0 ω = 0)
    (hclock : ∀ i ω t,
      (∫ r in Ioc 0 t, (H i r ω) ^ 2 ∂timeMeasure) = (A i t ω : ℝ))
    (henergy : ∀ i ω t, IntegrableOn (fun r => (H i r ω) ^ 2) (Ioc 0 t) timeMeasure)
    (t : ℝ≥0) (ω : Ω) :
    (∑ i, ∫ r in Ioc 0 t, (stepIntegrand g θ H A i r ω) ^ 2 ∂timeMeasure) =
      stepBracket g θ A t ω := by
  classical
  have hint (i : ι) (j : κ) : IntegrableOn
      (fun r => if g.channel j = i ∧ g.lower j < A i r ω ∧ A i r ω ≤ g.upper j
        then θ j ^ 2 * (H i r ω) ^ 2 else 0) (Ioc 0 t) timeMeasure := by
    by_cases hj : g.channel j = i
    · have h1 := ((henergy i ω t).const_mul (θ j ^ 2)).indicator
          ((measurableSet_lt measurable_const (hc i ω).measurable).inter
            (measurableSet_le (hc i ω).measurable measurable_const) :
          MeasurableSet ({r | g.lower j < A i r ω} ∩ {r | A i r ω ≤ g.upper j}))
      refine h1.congr (Filter.Eventually.of_forall fun r => ?_)
      beta_reduce
      by_cases hr : g.lower j < A i r ω ∧ A i r ω ≤ g.upper j
      · rw [Set.indicator_of_mem (show r ∈ {a | g.lower j < A i a ω} ∩ {a | A i a ω ≤ g.upper j}
          from hr), if_pos ⟨hj, hr⟩]
      · rw [Set.indicator_of_notMem (show r ∉ {a | g.lower j < A i a ω} ∩
          {a | A i a ω ≤ g.upper j} from fun hh => hr hh), if_neg (fun h => hr h.2)]
    · simpa only [hj, false_and, if_false] using
        (integrable_zero ℝ≥0 ℝ (timeMeasure.restrict (Ioc 0 t)))
  calc
    _ = ∑ i, ∑ j, ∫ r in Ioc 0 t,
        if g.channel j = i ∧ g.lower j < A i r ω ∧ A i r ω ≤ g.upper j
          then θ j ^ 2 * (H i r ω) ^ 2 else 0 ∂timeMeasure := by
      apply Finset.sum_congr rfl
      intro i _
      simp_rw [stepIntegrand_sq]
      exact integral_finsetSum _ (fun j _ => hint i j)
    _ = ∑ j, ∑ i, ∫ r in Ioc 0 t,
        if g.channel j = i ∧ g.lower j < A i r ω ∧ A i r ω ≤ g.upper j
          then θ j ^ 2 * (H i r ω) ^ 2 else 0 ∂timeMeasure := Finset.sum_comm
    _ = stepBracket g θ A t ω := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_eq_single (g.channel j)]
      · simp only [true_and]
        have heq : (fun r => if g.lower j < A (g.channel j) r ω ∧
            A (g.channel j) r ω ≤ g.upper j
            then θ j ^ 2 * (H (g.channel j) r ω) ^ 2 else 0) =
            fun r => θ j ^ 2 * (if g.lower j < A (g.channel j) r ω ∧
              A (g.channel j) r ω ≤ g.upper j then (H (g.channel j) r ω) ^ 2 else 0) := by
          funext r
          split_ifs <;> simp
        have hce := clockWindow_energy (A (g.channel j)) (Function.uncurry (H (g.channel j)))
          (hc _) (hm _) (hz _) (hclock _) (henergy _) (g.ordered j) t ω
        simp only [Function.uncurry_apply_pair] at hce
        rw [heq, integral_const_mul, hce, NNReal.coe_min, NNReal.coe_min]
      · intro i _ hij
        simp [Ne.symm hij]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))

end Ripple.Stochastic.Knight
