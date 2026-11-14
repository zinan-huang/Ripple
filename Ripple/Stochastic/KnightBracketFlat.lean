import Ripple.Stochastic.KnightStoppedClock
import Ripple.Stochastic.KnightClockFibres
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Flat-clock events from clock-stopped second moments

The event that a clock is flat over an interval need not belong to the past
sigma-algebra. We compare its indicator times the original squared increment
with the square of a stopped increment on the original probability space.
Letting the clock cap decrease to zero proves endpoint equality on that event.
The countable dense-time lifting then gives one all-time exceptional set.

The stochastic input is an explicit second-moment bound for the actual
clock-stopped path defined below. Its derivation from the installed stochastic
integral's random-stopping identity and isometry remains a separate producer.
No finite-channel exponential is used.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace Ripple.ProbabilityTheory
open Ripple.Analysis

private theorem ennreal_eq_zero_of_le_every_positive {x : ℝ≥0∞}
    (hx : ∀ ε : ℝ, 0 < ε → x ≤ ENNReal.ofReal ε) : x = 0 := by
  have hfin : x ≠ ⊤ := ne_top_of_le_ne_top
    (show (1 : ℝ≥0∞) ≠ ⊤ by norm_num) (by simpa using hx 1 zero_lt_one)
  by_contra hzero
  have hpos : 0 < x.toReal := ENNReal.toReal_pos hzero hfin
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hx (x.toReal / 2) (by positivity))
  rw [ENNReal.toReal_ofReal (by positivity)] at h
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- At fixed ordered endpoints, the cap estimate annihilates the increment on
flat-clock paths. The cap estimate is unconditional; no restriction of the
martingale to a future event occurs. -/
theorem ae_eq_on_flat_of_stopped_secondMoment
    {A : ℝ≥0 → Ω → ℝ≥0} {M : ℝ≥0 → Ω → ℝ}
    (hA : ∀ t, Measurable (A t)) (hM : ∀ t, Measurable (M t))
    (hm : ∀ᵐ ω ∂P, Monotone (fun t => A t ω))
    {s t : ℝ≥0} (hst : s ≤ t)
    (hStoppedSecondMoment : ∀ ε : ℝ≥0, 0 < ε →
      (∫⁻ ω, (‖clockStoppedPath (fun r => M (s + r) ω - M s ω)
        (shiftedClock (fun r => A r ω) s) ε (t - s)‖₊ : ℝ≥0∞) ^ 2 ∂P) ≤ ε) :
    ∀ᵐ ω ∂P, A s ω = A t ω → M s ω = M t ω := by
  let E : Set Ω := {ω | A s ω = A t ω}
  let D : Ω → ℝ≥0∞ := E.indicator (fun ω => (‖M t ω - M s ω‖₊ : ℝ≥0∞) ^ 2)
  have hE : MeasurableSet E := measurableSet_eq_fun (hA s) (hA t)
  have hD : Measurable D :=
    ((ENNReal.continuous_coe.measurable.comp ((hM t).sub (hM s)).nnnorm).pow_const 2).indicator hE
  have hbound : ∀ ε : ℝ, 0 < ε → (∫⁻ ω, D ω ∂P) ≤ ENNReal.ofReal ε := by
    intro ε hε
    let e : ℝ≥0 := ⟨ε, hε.le⟩
    have he : 0 < e := hε
    have hcmp : (∫⁻ ω, D ω ∂P) ≤
        ∫⁻ ω, (‖clockStoppedPath (fun r => M (s + r) ω - M s ω)
          (shiftedClock (fun r => A r ω) s) e (t - s)‖₊ : ℝ≥0∞) ^ 2 ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hm] with ω hω
      by_cases hflat : ω ∈ E
      · rw [show D ω = (‖M t ω - M s ω‖₊ : ℝ≥0∞) ^ 2 by
          simp [D, hflat]]
        have h : clockStoppedPath (fun r => M (s + r) ω - M s ω)
            (shiftedClock (fun r => A r ω) s) e (t - s) = M t ω - M s ω :=
          shifted_stopped_increment_of_flat (M := fun t => M t ω) (A := fun t => A t ω)
            hω hst hflat
        rw [h]
      · simp [D, hflat]
    have hb := hcmp.trans (hStoppedSecondMoment e he)
    change (∫⁻ ω, D ω ∂P) ≤ ENNReal.ofReal (e : ℝ)
    simpa only [ENNReal.ofReal_coe_nnreal] using hb
  have hzero : ∫⁻ ω, D ω ∂P = 0 := ennreal_eq_zero_of_le_every_positive hbound
  have hae : D =ᵐ[P] 0 := (lintegral_eq_zero_iff' hD.aemeasurable).mp hzero
  filter_upwards [hae] with ω hω hflat
  have hmem : ω ∈ E := hflat
  have hsquare : (‖M t ω - M s ω‖₊ : ℝ≥0∞) ^ 2 = 0 := by
    simpa [D, hmem] using hω
  have hdiff : M t ω - M s ω = 0 := by simpa using hsquare
  exact (sub_eq_zero.mp hdiff).symm

/-- The concrete clock-stopped second-moment estimate, on a countable dense
set of deterministic endpoints, gives the simultaneous bracket-flat property.
The stochastic stopping/isometry estimate is the only stochastic input beyond
slice measurability and path regularity. -/
theorem ae_constantOnClockFibres_of_stopped_secondMoment
    {A : ℝ≥0 → Ω → ℝ≥0} {M : ℝ≥0 → Ω → ℝ}
    (d : ℕ → ℝ≥0) (hd : DenseRange d)
    (hA : ∀ t, Measurable (A t)) (hM : ∀ t, Measurable (M t))
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    (hm : ∀ᵐ ω ∂P, Monotone (fun t => A t ω))
    (hStoppedSecondMoment : ∀ i j, d i ≤ d j → ∀ ε : ℝ≥0, 0 < ε →
      (∫⁻ ω, (‖clockStoppedPath (fun r => M (d i + r) ω - M (d i) ω)
        (shiftedClock (fun r => A r ω) (d i)) ε (d j - d i)‖₊ : ℝ≥0∞) ^ 2 ∂P) ≤ ε) :
    ∀ᵐ ω ∂P, ConstantOnClockFibres (fun t => A t ω) (fun t => M t ω) := by
  apply ae_constantOnClockFibres_of_dense d hd hc hm
  intro i j
  rcases le_total (d i) (d j) with hij | hji
  · exact ae_eq_on_flat_of_stopped_secondMoment hA hM hm hij
      (hStoppedSecondMoment i j hij)
  · filter_upwards [ae_eq_on_flat_of_stopped_secondMoment hA hM hm hji
      (hStoppedSecondMoment j i hji)] with ω hω heq
    exact (hω heq.symm).symm

end Ripple.ProbabilityTheory
