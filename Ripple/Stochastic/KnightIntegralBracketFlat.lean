import Ripple.Stochastic.KnightIntegralConvergence
import Ripple.Stochastic.KnightClockFibres
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Constancy of the actual integral on clock fibres

Post-start integrands use the original Brownian motion and filtration. Their
clock is the original clock with its value at the deterministic start removed.
Inverse-clock second moments then annihilate increments on flat-clock events.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace Ripple.Stochastic.KnightIntegralBracketFlat
open Ripple.Analysis Ripple.ProbabilityTheory
open FilteredItoIntegralL2 FilteredItoIntegralCLM
open ContinuousItoElementary AdaptedContinuousSpace ContinuousItoConsistency
open ContinuousItoStoppingGrid ContinuousItoStopping StoppedPredictableIntegrand
open ContinuousItoHalfLineStopping ClockStoppedIntegral KnightIntegralConvergence

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
  [IsFilteredPreBrownian B F μ]

/-- Retain only the integrand after a deterministic start time. -/
def postStartRaw (s : ℝ≥0) (H : ℝ≥0 × Ω → ℝ) : ℝ≥0 × Ω → ℝ :=
  (Set.Ioi s ×ˢ (Set.univ : Set Ω)).indicator H

/-- Its cumulative energy starts only after s. -/
def postStartClock (s : ℝ≥0) (A : ℝ≥0 → Ω → ℝ≥0) (r : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  A r ω - A (min r s) ω

theorem postStartRaw_stronglyMeasurable (s : ℝ≥0) {H : ℝ≥0 × Ω → ℝ}
    (hHsm : StronglyMeasurable[F.predictable] H) :
    StronglyMeasurable[F.predictable] (postStartRaw s H) :=
  hHsm.indicator (measurableSet_predictable_Ioi_prod (𝓕 := F) MeasurableSet.univ)

theorem postStartRaw_memLp (s : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {H : ℝ≥0 × Ω → ℝ}
    (hH : ∀ n : ℕ, MemLp H 2
      (trimMeasure_T (𝓖 := F) (μ := μ) (n : ℝ≥0) hBmeas)) (n : ℕ) :
    MemLp (postStartRaw s H) 2
      (trimMeasure_T (𝓖 := F) (μ := μ) (n : ℝ≥0) hBmeas) :=
  (hH n).indicator (measurableSet_predictable_Ioi_prod (𝓕 := F) MeasurableSet.univ)

theorem postStartClock_adapted (s : ℝ≥0) {A : ℝ≥0 → Ω → ℝ≥0}
    (ha : Adapted F A) : Adapted F (postStartClock s A) := by
  intro r
  exact (ha r).sub ((ha (min r s)).mono (F.mono (min_le_left _ _)) le_rfl)

theorem postStartClock_continuous (s : ℝ≥0) {A : ℝ≥0 → Ω → ℝ≥0}
    (hc : ∀ ω, Continuous (fun r => A r ω)) (ω : Ω) :
    Continuous (fun r => postStartClock s A r ω) :=
  (hc ω).sub ((hc ω).comp (continuous_id.min continuous_const))

theorem postStartClock_monotone (s : ℝ≥0) {A : ℝ≥0 → Ω → ℝ≥0}
    (hm : ∀ ω, Monotone (fun r => A r ω)) (ω : Ω) :
    Monotone (fun r => postStartClock s A r ω) := by
  intro r q hrq
  by_cases hqs : q ≤ s
  · have hrs := hrq.trans hqs
    simp [postStartClock, min_eq_left hrs, min_eq_left hqs]
  · by_cases hrs : r ≤ s
    · simp only [postStartClock, min_eq_left hrs, tsub_self]
      exact zero_le
    · simp only [postStartClock, min_eq_right (le_of_not_ge hrs),
        min_eq_right (le_of_not_ge hqs)]
      exact tsub_le_tsub_right (hm ω hrq) _

@[simp] theorem postStartClock_zero (s : ℝ≥0) (A : ℝ≥0 → Ω → ℝ≥0) (ω : Ω) :
    postStartClock s A 0 ω = 0 := by simp [postStartClock]

/-- Exact deterministic energy identity, using pathwise integrability only
to subtract the two ordinary Bochner integrals. -/
theorem postStartRaw_energy (s : ℝ≥0) (H : ℝ≥0 × Ω → ℝ)
    (A : ℝ≥0 → Ω → ℝ≥0)
    (hm : ∀ ω, Monotone (fun r => A r ω))
    (hpath : ∀ ω r, IntegrableOn (fun v => H (v, ω) ^ 2) (Set.Ioc 0 r) timeMeasure)
    (hclock : ∀ ω r, (∫ v in Set.Ioc 0 r, H (v, ω) ^ 2 ∂timeMeasure) = (A r ω : ℝ))
    (ω : Ω) (r : ℝ≥0) :
    (∫ v in Set.Ioc 0 r, postStartRaw s H (v, ω) ^ 2 ∂timeMeasure) =
      (postStartClock s A r ω : ℝ) := by
  have heq : (fun v => postStartRaw s H (v, ω) ^ 2) =
      fun v => H (v, ω) ^ 2 - (Set.Iic s).indicator (fun v => H (v, ω) ^ 2) v := by
    funext v
    by_cases hvs : v ≤ s
    · simp [postStartRaw, hvs, not_lt_of_ge hvs]
    · simp [postStartRaw, hvs, lt_of_not_ge hvs]
  rw [heq, integral_sub (hpath ω r) ((hpath ω r).indicator measurableSet_Iic),
    setIntegral_indicator measurableSet_Iic]
  have hinter : Set.Ioc (0 : ℝ≥0) r ∩ Set.Iic s = Set.Ioc 0 (min r s) := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic, le_min_iff]
    tauto
  rw [hinter, hclock, hclock, postStartClock,
    NNReal.coe_sub (hm ω (min_le_left r s))]

/-- Selected path representatives respect subtraction outside one null set. -/
theorem representative_sub_ae {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (X Y : PathLp K μ) :
    representative (X - Y) =ᵐ[μ] fun ω => representative X ω - representative Y ω := by
  filter_upwards [representative_ae (X - Y), Lp.coeFn_sub X Y,
    representative_ae X, representative_ae Y] with ω hd hs hX hY
  exact hd.symm.trans (hs.trans (congrArg₂ (fun x y : C(K, ℝ) => x - y) hX hY))

section IntegralIdentity
variable (hB : ∀ ω, Continuous (fun t => B t ω))
  (hBmeas : ∀ t, Measurable (B t))
  (H : ℝ≥0 × Ω → ℝ)
  (hH : ∀ n : ℕ, MemLp H 2
    (trimMeasure_T (𝓖 := F) (μ := μ) (n : ℝ≥0) hBmeas))

/-- The post-start raw class is the original class minus its deterministic stop. -/
theorem integerIntegrand_postStart (s : ℝ≥0) (n : ℕ) :
    integerIntegrand hBmeas (postStartRaw s H) (postStartRaw_memLp s hBmeas hH) n =
      integerIntegrand hBmeas H hH n -
        stoppedIntegrand (n : ℝ≥0) hBmeas (isStoppingTime_const F s)
          (integerIntegrand hBmeas H hH n) := by
  apply Lp.ext
  filter_upwards [(postStartRaw_memLp s hBmeas hH n).coeFn_toLp,
    Lp.coeFn_sub (integerIntegrand hBmeas H hH n)
      (stoppedIntegrand (n : ℝ≥0) hBmeas (isStoppingTime_const F s)
        (integerIntegrand hBmeas H hH n)),
    (hH n).coeFn_toLp,
    stoppedIntegrand_coeFn (n : ℝ≥0) hBmeas (isStoppingTime_const F s)
      (integerIntegrand hBmeas H hH n),
    BoundedPredictableApproximation.ae_window (F := F) (μ := μ) (n : ℝ≥0) hBmeas]
      with z hp hd hraw hstop hwin
  have hp' : (integerIntegrand hBmeas (postStartRaw s H) (postStartRaw_memLp s hBmeas hH) n :
      ℝ≥0 × Ω → ℝ) z = postStartRaw s H z := hp
  rw [hp', hd, Pi.sub_apply, hstop]
  change postStartRaw s H z =
    integerIntegrand hBmeas H hH n z -
      (stoppingRegion (fun _ : Ω => (s : WithTop ℝ≥0))).indicator
        (integerIntegrand hBmeas H hH n) z
  have hraw' : integerIntegrand hBmeas H hH n z = H z := hraw
  rw [hraw']
  by_cases hzs : z.1 ≤ s
  · have hm : z ∈ stoppingRegion (fun _ : Ω => (s : WithTop ℝ≥0)) :=
      ⟨hwin.1, WithTop.coe_le_coe.2 hzs⟩
    rw [Set.indicator_of_mem hm, hraw', sub_self]
    simp [postStartRaw, not_lt_of_ge hzs]
  · have hm : z ∉ stoppingRegion (fun _ : Ω => (s : WithTop ℝ≥0)) := fun h =>
      hzs (WithTop.coe_le_coe.1 h.2)
    rw [Set.indicator_of_notMem hm, sub_zero]
    simp [postStartRaw, lt_of_not_ge hzs]

/-- The actual post-start integral is the original integral minus its value
at the deterministic stopped argument, simultaneously in all half-line times. -/
theorem halfLineIto_postStart (s : ℝ≥0) :
    ∀ᵐ ω ∂μ, ∀ r : ℝ≥0,
      halfLineIto hB hBmeas (postStartRaw s H) (postStartRaw_memLp s hBmeas hH) r ω =
        halfLineIto hB hBmeas H hH r ω - halfLineIto hB hBmeas H hH (min r s) ω := by
  have hfinite : ∀ᵐ ω ∂μ, ∀ n : ℕ, ∀ r : Set.Icc (0 : ℝ≥0) (n : ℝ≥0),
      integerItoPath hB hBmeas (postStartRaw s H) (postStartRaw_memLp s hBmeas hH) n ω r =
        integerItoPath hB hBmeas H hH n ω r -
          integerItoPath hB hBmeas H hH n ω
            (stoppedWindowTime (n : ℝ≥0) (fun _ => s) ω r) := by
    apply ae_all_iff.mpr
    intro n
    let φ := integerIntegrand hBmeas H hH n
    have hsub := representative_sub_ae (continuousIto (n : ℝ≥0) hB hBmeas φ)
      (continuousIto (n : ℝ≥0) hB hBmeas
        (stoppedIntegrand (n : ℝ≥0) hBmeas (isStoppingTime_const F s) φ))
    have hstop' := continuousIto_stopped (n : ℝ≥0) hB hBmeas
      (isStoppingTime_const F s) φ
    change ∀ᵐ ω ∂μ, ∀ r : Set.Icc (0 : ℝ≥0) (n : ℝ≥0),
      representative (continuousIto (n : ℝ≥0) hB hBmeas
        (integerIntegrand hBmeas (postStartRaw s H) (postStartRaw_memLp s hBmeas hH) n)) ω r = _
    rw [integerIntegrand_postStart hBmeas H hH s n, map_sub]
    filter_upwards [hsub, hstop'] with ω hsubω hstopω r
    rw [hsubω]
    change representative (continuousIto (n : ℝ≥0) hB hBmeas φ) ω r -
      representative (continuousIto (n : ℝ≥0) hB hBmeas
        (stoppedIntegrand (n : ℝ≥0) hBmeas (isStoppingTime_const F s) φ)) ω r = _
    rw [hstopω]
    have htime : stoppedWindowTime (n : ℝ≥0)
        (cappedStopTime (n : ℝ≥0) (fun _ : Ω => (s : WithTop ℝ≥0))) ω r =
          stoppedWindowTime (n : ℝ≥0) (fun _ => s) ω r := by
      apply Subtype.ext
      change min r.val (cappedStopTime (n : ℝ≥0) (fun _ : Ω => (s : WithTop ℝ≥0)) ω) =
        min r.val s
      rw [ContinuousItoHalfLineStopping.cappedStopTime_min r.property.2]
      apply WithTop.coe_injective
      simp only [coe_cappedStopTime, WithTop.coe_min, min_comm]
    rw [htime]
    rfl
  filter_upwards [hfinite,
    halfLineIto_integer_agreement hB hBmeas (postStartRaw s H) (postStartRaw_memLp s hBmeas hH),
    halfLineIto_integer_agreement hB hBmeas H hH] with ω hfin hpost horig r
  let n := coveringHorizon r
  let rr : Set.Icc (0 : ℝ≥0) (n : ℝ≥0) := ⟨r, zero_le, (lt_coveringHorizon r).le⟩
  let rs := stoppedWindowTime (n : ℝ≥0) (fun _ : Ω => s) ω rr
  exact (hpost n rr).trans ((hfin n rr).trans
    (congrArg₂ (fun a b : ℝ => a - b) (horig n rr).symm (horig n rs).symm))

end IntegralIdentity

private theorem ennreal_eq_zero_of_le_positive {x : ℝ≥0∞}
    (hx : ∀ ε : ℝ, 0 < ε → x ≤ ENNReal.ofReal ε) : x = 0 := by
  have hfin : x ≠ ⊤ := ne_top_of_le_ne_top
    (show (1 : ℝ≥0∞) ≠ ⊤ by norm_num) (by simpa using hx 1 zero_lt_one)
  by_contra hzero
  have hpos : 0 < x.toReal := ENNReal.toReal_pos hzero hfin
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hx (x.toReal / 2) (by positivity))
  rw [ENNReal.toReal_ofReal (by positivity)] at h
  linarith

section BracketFlat
variable (hB : ∀ ω, Continuous (fun t => B t ω))
  (hBmeas : ∀ t, Measurable (B t)) [F.IsRightContinuous]
  (A : ℝ≥0 → Ω → ℝ≥0) (ha : Adapted F A)
  (hc : ∀ ω, Continuous (fun r => A r ω))
  (hm : ∀ ω, Monotone (fun r => A r ω))
  (H : ℝ≥0 × Ω → ℝ) (hHsm : StronglyMeasurable[F.predictable] H)
  (hH : ∀ n : ℕ, MemLp H 2
    (trimMeasure_T (𝓖 := F) (μ := μ) (n : ℝ≥0) hBmeas))
  (hpath : ∀ ω r, IntegrableOn (fun v => H (v, ω) ^ 2) (Set.Ioc 0 r) timeMeasure)
  (hclock : ∀ ω r, (∫ v in Set.Ioc 0 r, H (v, ω) ^ 2 ∂timeMeasure) = (A r ω : ℝ))

include ha hc hm hHsm hpath hclock in
/-- A flat clock interval annihilates the actual stochastic-integral increment.
The auxiliary second moment is produced from the installed inverse-clock stop. -/
theorem halfLineIto_ae_eq_on_flat {s t : ℝ≥0} (hst : s ≤ t) :
    ∀ᵐ ω ∂μ, A s ω = A t ω →
      halfLineIto hB hBmeas H hH s ω = halfLineIto hB hBmeas H hH t ω := by
  let M := halfLineIto hB hBmeas H hH
  let K := postStartRaw s H
  let hK := postStartRaw_memLp s hBmeas hH
  let C := postStartClock s A
  have hCa : Adapted F C := postStartClock_adapted s ha
  have hCc : ∀ ω, Continuous (fun r => C r ω) := postStartClock_continuous s hc
  have hCm : ∀ ω, Monotone (fun r => C r ω) := postStartClock_monotone s hm
  have hCz : ∀ ω, C 0 ω = 0 := postStartClock_zero s A
  have hCenergy : ∀ ω r, (∫ v in Set.Ioc 0 r, K (v, ω) ^ 2 ∂timeMeasure) = (C r ω : ℝ) :=
    postStartRaw_energy s H A hm hpath hclock
  let E : Set Ω := {ω | A s ω = A t ω}
  let D : Ω → ℝ≥0∞ := E.indicator (fun ω => (‖M t ω - M s ω‖₊ : ℝ≥0∞) ^ 2)
  have hE : MeasurableSet E := measurableSet_eq_fun
    ((ha s).mono (F.le s) le_rfl) ((ha t).mono (F.le t) le_rfl)
  have hMmeas : ∀ r, Measurable (M r) := fun r =>
    (halfLineIto_stronglyMeasurable hB hBmeas H hH r).measurable
  have hD : Measurable D :=
    ((ENNReal.continuous_coe.measurable.comp ((hMmeas t).sub (hMmeas s)).nnnorm).pow_const 2).indicator hE
  have hbound : ∀ ε : ℝ, 0 < ε → (∫⁻ ω, D ω ∂μ) ≤ ENNReal.ofReal ε := by
    intro ε hε
    let e : ℝ≥0 := ⟨ε, hε.le⟩
    let σ := clockInverseTime C e
    have hσ : IsStoppingTime F σ := clockInverseTime_isStoppingTime hCa hCc hCm hCz e
    let L := halfLineIto hB hBmeas (stoppedRawIntegrand σ K)
      (stoppedRawIntegrand_memLp hBmeas hσ K hK)
    have hmoment : (∫⁻ ω, (‖L t ω‖₊ : ℝ≥0∞) ^ 2 ∂μ) ≤ e :=
      clockStoppedHalfLineIto_secondMoment_le hB hBmeas C hCa hCc hCm hCz K
        (postStartRaw_stronglyMeasurable s hHsm) hK hCenergy e t
    have hcmp : (∫⁻ ω, D ω ∂μ) ≤ ∫⁻ ω, (‖L t ω‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [halfLineIto_stoppedRaw hB hBmeas hσ K hK,
        halfLineIto_postStart hB hBmeas H hH s] with ω hstop hpost
      by_cases hflat : ω ∈ E
      · have hCzero : C t ω = 0 := by
          change A t ω - A (min t s) ω = 0
          rw [min_eq_right hst, show A s ω = A t ω from hflat, tsub_self]
        have hinv : (t : ℝ≥0∞) ≤ clockInverse (fun r => C r ω) e :=
          (le_clockInverse_iff (hCc ω) (hCm ω) (hCz ω) e t).mpr
            (by rw [hCzero]; exact zero_le)
        have hcap : cappedStopTime t σ ω = t :=
          (cappedStopTime_clockInverseTime t C e ω).trans (clockStoppedTime_eq_self_of_le hinv)
        have heq : L t ω = M t ω - M s ω := by
          change halfLineIto hB hBmeas (stoppedRawIntegrand σ K)
            (stoppedRawIntegrand_memLp hBmeas hσ K hK) t ω = _
          rw [hstop t, hcap, hpost t, min_eq_right hst]
        simp only [D, Set.indicator_of_mem hflat, heq, le_refl]
      · simp [D, hflat]
    have hb := hcmp.trans hmoment
    change (∫⁻ ω, D ω ∂μ) ≤ ENNReal.ofReal (e : ℝ)
    simpa only [ENNReal.ofReal_coe_nnreal] using hb
  have hzero : ∫⁻ ω, D ω ∂μ = 0 := ennreal_eq_zero_of_le_positive hbound
  have hae : D =ᵐ[μ] 0 := (lintegral_eq_zero_iff' hD.aemeasurable).mp hzero
  filter_upwards [hae] with ω hω hflat
  have hmem : ω ∈ E := hflat
  have hsquare : (‖M t ω - M s ω‖₊ : ℝ≥0∞) ^ 2 = 0 := by simpa [D, hmem] using hω
  have hdiff : M t ω - M s ω = 0 := by simpa using hsquare
  exact (sub_eq_zero.mp hdiff).symm

include ha hc hm hHsm hpath hclock in
/-- The actual half-line integral is almost surely constant on every fibre
of its actual cumulative energy clock. No stopped-moment premise is assumed. -/
theorem halfLineIto_ae_constantOnClockFibres :
    ∀ᵐ ω ∂μ, ConstantOnClockFibres (fun r => A r ω)
      (fun r => halfLineIto hB hBmeas H hH r ω) := by
  apply ae_constantOnClockFibres_of_dense (TopologicalSpace.denseSeq ℝ≥0)
    (TopologicalSpace.denseRange_denseSeq ℝ≥0)
    (halfLineIto_ae_continuous hB hBmeas H hH) (ae_of_all μ hm)
  intro i j
  rcases le_total (TopologicalSpace.denseSeq ℝ≥0 i) (TopologicalSpace.denseSeq ℝ≥0 j) with hij | hji
  · exact halfLineIto_ae_eq_on_flat hB hBmeas A ha hc hm H hHsm hH hpath hclock hij
  · filter_upwards [halfLineIto_ae_eq_on_flat hB hBmeas A ha hc hm H hHsm hH hpath hclock hji]
      with ω hω heq
    exact (hω heq.symm).symm

end BracketFlat
end Ripple.Stochastic.KnightIntegralBracketFlat
