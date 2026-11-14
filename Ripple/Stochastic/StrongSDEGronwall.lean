import Ripple.Kurtz.IntegralGronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Gronwall uniqueness for strong SDE solutions

The zero-initial-error integral Gronwall estimate and a
conditional transfer to equality at each fixed time.

A stochastic application must construct the moment function and prove its
continuity, nonnegativity, integral inequality, and the implication from zero
moment to almost-everywhere equality. These producers are not constructed here.
One may use a continuous stopped-process moment function on the whole real line:
extend its values below zero constantly and stop its time argument above the
terminal time. The agreement and continuity of that extension remain obligations
of the application.
-/

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace Ripple.Stochastic.StrongSDE

/-- A continuous, nonnegative function dominated by its own constant-coefficient
integral vanishes throughout the time window. Global continuity discharges all
FTC plumbing in `Ripple.Kurtz.integral_gronwall`. -/
theorem continuous_integral_gronwall_zero {u : ℝ → ℝ} {T C : ℝ}
    (hMomentContinuous : Continuous u) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hMomentNonnegative : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ u t)
    (hDifferenceIntegral : ∀ t ∈ Icc (0 : ℝ) T,
      u t ≤ ∫ s in (0 : ℝ)..t, C * u s) :
    ∀ t ∈ Icc (0 : ℝ) T, u t = 0 := by
  have hg : Continuous (fun s => C * u s) := continuous_const.mul hMomentContinuous
  have hp : Continuous (fun t => ∫ s in (0 : ℝ)..t, C * u s) := by
    exact intervalIntegral.continuous_primitive (fun x y => hg.intervalIntegrable x y) 0
  intro t ht
  have hupper : u t ≤ (0 : ℝ) * Real.exp (C * t) :=
    Ripple.Kurtz.integral_gronwall hT (le_refl 0) hC hMomentNonnegative
      (fun s hs => by simpa only [zero_add] using hDifferenceIntegral s hs)
      (fun x _ => hg.intervalIntegrable 0 x)
      (fun _ _ => hg.continuousAt.continuousWithinAt)
      (fun x _ => hg.stronglyMeasurableAtFilter volume (nhdsWithin x (Ioi x)))
      (continuous_const.add hp).continuousOn t ht
  exact le_antisymm (by simpa only [zero_mul] using hupper) (hMomentNonnegative t ht)

/-- Fixed-time uniqueness transfer. For example, `u t` may be the expected square
of the path supremum difference up to time `t`; the moment theory must supply
`hZeroMoment`. Its exact identity with that expectation, finite integrability,
and the derivation of `hDifferenceIntegral` are not hidden conclusions here.

The quantifier order is deliberate: this proves equality almost everywhere at
each fixed time. A single event on which all times agree additionally requires
continuous sample paths and a countable dense-time argument, or a direct
zero-supremum-moment implication. -/
theorem fixed_time_ae_eq_of_difference_integral
    {Ω E : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : ℝ → Ω → E) {u : ℝ → ℝ} {T C : ℝ}
    (hMomentContinuous : Continuous u) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hMomentNonnegative : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ u t)
    (hDifferenceIntegral : ∀ t ∈ Icc (0 : ℝ) T,
      u t ≤ ∫ s in (0 : ℝ)..t, C * u s)
    (hZeroMoment : ∀ t ∈ Icc (0 : ℝ) T, u t = 0 → X t =ᵐ[P] Y t) :
    ∀ t ∈ Icc (0 : ℝ) T, X t =ᵐ[P] Y t := by
  intro t ht
  exact hZeroMoment t ht
    (continuous_integral_gronwall_zero hMomentContinuous hT hC
      hMomentNonnegative hDifferenceIntegral t ht)

/-- Vector-valued dense-time upgrade. Use the compact time interval as `τ` to
obtain indistinguishability on a horizon after the preceding Gronwall theorem. -/
theorem indistinguishable_of_dense
    {τ Ω E : Type*} [TopologicalSpace τ] [MeasurableSpace Ω]
    [NormedAddCommGroup E] {P : Measure Ω} {X Y : τ → Ω → E}
    (d : ℕ → τ) (hd : DenseRange d)
    (hX : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hY : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω))
    (hGrid : ∀ n, X (d n) =ᵐ[P] Y (d n)) :
    ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω := by
  have hall : ∀ᵐ ω ∂P, ∀ n, X (d n) ω = Y (d n) ω := ae_all_iff.mpr hGrid
  filter_upwards [hX, hY, hall] with ω hXω hYω hω
  have heq : (fun t => X t ω) = (fun t => Y t ω) :=
    hd.equalizer hXω hYω (funext hω)
  exact congrFun heq

end Ripple.Stochastic.StrongSDE
