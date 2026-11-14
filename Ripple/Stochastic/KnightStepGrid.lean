import Ripple.Analysis.ClockInverse
import Ripple.Stochastic.KnightTerminalMGF
import Ripple.Stochastic.GaussianFromMGF
import Mathlib.Tactic

/-!
# The finite rectangular grid in Knight's argument

Different channels can have different internal grids. Physical time is shared
by every stopped summand. The candidate bracket is the sum of the clipped
clock increments, weighted by squared coefficients.

This file proves its bounds and its eventual deterministic value, and proves
that the stopped sum eventually equals the required linear combination of
inverse-clock increments. Identification of this candidate bracket with the
bracket of the stochastic integral, and normalization of its exponentials,
are separate stochastic-integral obligations.
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped NNReal ENNReal Topology

namespace Ripple.Stochastic.Knight

open Ripple.Analysis

/-- A finite collection of intervals, disjoint within each channel.
Zero-length intervals are allowed; no positive-rate premise is imposed. -/
structure IntervalGrid (ι κ : Type*) where
  channel : κ → ι
  lower : κ → ℝ≥0
  upper : κ → ℝ≥0
  ordered : ∀ j, lower j ≤ upper j
  separated : ∀ j k, j ≠ k → channel j = channel k →
    upper j ≤ lower k ∨ upper k ≤ lower j

variable {ι κ Ω : Type*} [Fintype κ]

noncomputable section

/-- The finite inverse-time value; callers must prove finiteness before
using its stopping-time interpretation. -/
def inverseTime (A : ι → ℝ≥0 → Ω → ℝ≥0) (i : ι) (u : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (clockInverse (fun t => A i t ω) u).toNNReal

def rawChange (M : ι → ℝ≥0 → Ω → ℝ)
    (A : ι → ℝ≥0 → Ω → ℝ≥0) (i : ι) (u : ℝ≥0) (ω : Ω) : ℝ :=
  M i (inverseTime A i u ω) ω

/-- The common-physical-time stopped sum. -/
def stepSum (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (M : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ j, θ j * (M (g.channel j) (min t (inverseTime A (g.channel j) (g.upper j) ω)) ω -
    M (g.channel j) (min t (inverseTime A (g.channel j) (g.lower j) ω)) ω)

/-- The linear combination of the rectangular inverse-clock increments. -/
def terminalSum (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (M : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0) (ω : Ω) : ℝ :=
  ∑ j, θ j * (rawChange M A (g.channel j) (g.upper j) ω -
    rawChange M A (g.channel j) (g.lower j) ω)

/-- Candidate bracket in the original, common physical time. -/
def stepBracket (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (A : ι → ℝ≥0 → Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ j, θ j ^ 2 * (((min (A (g.channel j) t ω) (g.upper j) : ℝ≥0) : ℝ) -
    ((min (A (g.channel j) t ω) (g.lower j) : ℝ≥0) : ℝ))

/-- Deterministic terminal variance of the weighted grid. -/
def gridVariance (g : IntervalGrid ι κ) (θ : κ → ℝ) : ℝ :=
  ∑ j, θ j ^ 2 * ((g.upper j : ℝ) - (g.lower j : ℝ))

theorem gridVariance_nonneg (g : IntervalGrid ι κ) (θ : κ → ℝ) :
    0 ≤ gridVariance g θ := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (by exact_mod_cast g.ordered j))

theorem clipped_increment_nonneg {a l u : ℝ≥0} (h : l ≤ u) :
    0 ≤ (min a u : ℝ) - (min a l : ℝ) := by
  exact sub_nonneg.mpr (by exact_mod_cast min_le_min_left a h)

theorem clipped_increment_le {a l u : ℝ≥0} (h : l ≤ u) :
    (min a u : ℝ) - (min a l : ℝ) ≤ (u : ℝ) - (l : ℝ) := by
  by_cases hal : a ≤ l
  · rw [min_eq_left (by exact_mod_cast hal.trans h : (a : ℝ) ≤ u),
      min_eq_left (by exact_mod_cast hal : (a : ℝ) ≤ l), sub_self]
    exact sub_nonneg.mpr (by exact_mod_cast h)
  · rw [min_eq_right (by exact_mod_cast le_of_not_ge hal : (l : ℝ) ≤ a)]
    exact sub_le_sub_right (min_le_right _ _) _

theorem stepBracket_nonneg (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (A : ι → ℝ≥0 → Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    0 ≤ stepBracket g θ A t ω := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (sq_nonneg _) (clipped_increment_nonneg (g.ordered j))

theorem stepBracket_le_gridVariance (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (A : ι → ℝ≥0 → Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    stepBracket g θ A t ω ≤ gridVariance g θ := by
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (clipped_increment_le (g.ordered j)) (sq_nonneg _)

/-- A pathwise finite bound for all the inverse times in the grid. -/
def settleTime (g : IntervalGrid ι κ) (A : ι → ℝ≥0 → Ω → ℝ≥0) (ω : Ω) : ℝ≥0 :=
  Finset.univ.sup fun j => max (inverseTime A (g.channel j) (g.lower j) ω)
    (inverseTime A (g.channel j) (g.upper j) ω)

theorem inverseTime_le_settleTime (g : IntervalGrid ι κ)
    (A : ι → ℝ≥0 → Ω → ℝ≥0) (ω : Ω) (j : κ) :
    inverseTime A (g.channel j) (g.lower j) ω ≤ settleTime g A ω ∧
      inverseTime A (g.channel j) (g.upper j) ω ≤ settleTime g A ω := by
  have h : max (inverseTime A (g.channel j) (g.lower j) ω)
      (inverseTime A (g.channel j) (g.upper j) ω) ≤ settleTime g A ω :=
    Finset.le_sup (f := fun j => max (inverseTime A (g.channel j) (g.lower j) ω)
      (inverseTime A (g.channel j) (g.upper j) ω)) (Finset.mem_univ j)
  exact ⟨(le_max_left _ _).trans h, (le_max_right _ _).trans h⟩

theorem stepSum_eq_terminalSum (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (M : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0)
    (ω : Ω) {t : ℝ≥0} (ht : settleTime g A ω ≤ t) :
    stepSum g θ M A t ω = terminalSum g θ M A ω := by
  apply Finset.sum_congr rfl
  intro j _
  obtain ⟨hl, hu⟩ := inverseTime_le_settleTime g A ω j
  simp only [min_eq_right (hl.trans ht), min_eq_right (hu.trans ht), rawChange]

theorem stepBracket_eq_gridVariance (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (A : ι → ℝ≥0 → Ω → ℝ≥0) (ω : Ω)
    (hc : ∀ i, Continuous (fun t => A i t ω))
    (hm : ∀ i, Monotone (fun t => A i t ω)) (hz : ∀ i, A i 0 ω = 0)
    (hinf : ∀ j, (g.upper j : ℝ≥0∞) < terminalClock (fun t => A (g.channel j) t ω))
    {t : ℝ≥0} (ht : settleTime g A ω ≤ t) :
    stepBracket g θ A t ω = gridVariance g θ := by
  apply Finset.sum_congr rfl
  intro j _
  have hclock : A (g.channel j) (inverseTime A (g.channel j) (g.upper j) ω) ω =
      g.upper j := clock_at_clockInverse (hc _) (hm _) (hz _) (hinf j)
  have hu : g.upper j ≤ A (g.channel j) t ω := by
    rw [← hclock]
    exact hm _ ((inverseTime_le_settleTime g A ω j).2.trans ht)
  simp only [min_eq_right hu, min_eq_right ((g.ordered j).trans hu)]

theorem stepSum_tendsto (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (M : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0) (ω : Ω) :
    Tendsto (fun t => stepSum g θ M A t ω) atTop (𝓝 (terminalSum g θ M A ω)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (settleTime g A ω)] with t ht
  exact (stepSum_eq_terminalSum g θ M A ω ht).symm

theorem stepBracket_tendsto (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (A : ι → ℝ≥0 → Ω → ℝ≥0) (ω : Ω)
    (hc : ∀ i, Continuous (fun t => A i t ω))
    (hm : ∀ i, Monotone (fun t => A i t ω)) (hz : ∀ i, A i 0 ω = 0)
    (hinf : ∀ j, (g.upper j : ℝ≥0∞) < terminalClock (fun t => A (g.channel j) t ω)) :
    Tendsto (fun t => stepBracket g θ A t ω) atTop (𝓝 (gridVariance g θ)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (settleTime g A ω)] with t ht
  exact (stepBracket_eq_gridVariance g θ A ω hc hm hz hinf ht).symm

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The analytic Knight step, conditional on the common-time stochastic
exponential producer. The conclusion is an exact joint linear-combination
MGF, not separate marginal Gaussian claims. -/
theorem rectangular_increment_mgf
    (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (M : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0)
    (sample : ℕ → ℝ≥0) (hsample : Tendsto sample atTop atTop)
    (hc : ∀ᵐ ω ∂P, ∀ i, Continuous (fun t => A i t ω))
    (hm : ∀ᵐ ω ∂P, ∀ i, Monotone (fun t => A i t ω))
    (hz : ∀ᵐ ω ∂P, ∀ i, A i 0 ω = 0)
    (hinf : ∀ᵐ ω ∂P, ∀ j,
      (g.upper j : ℝ≥0∞) < terminalClock (fun t => A (g.channel j) t ω))
    (hY : ∀ n, AEStronglyMeasurable (stepSum g θ M A (sample n)) P)
    (hQ : ∀ n, AEStronglyMeasurable (stepBracket g θ A (sample n)) P)
    (hint : ∀ a n, Integrable (fun ω => Real.exp
      (a * stepSum g θ M A (sample n) ω -
        a ^ 2 * stepBracket g θ A (sample n) ω / 2)) P)
    (hmean : ∀ a n, (∫ ω, Real.exp
      (a * stepSum g θ M A (sample n) ω -
        a ^ 2 * stepBracket g θ A (sample n) ω / 2) ∂P) = 1) :
    Integrable (fun ω => Real.exp (terminalSum g θ M A ω)) P ∧
      (∫ ω, Real.exp (terminalSum g θ M A ω) ∂P) = Real.exp (gridVariance g θ / 2) := by
  have hYlim : ∀ᵐ ω ∂P, Tendsto (fun n => stepSum g θ M A (sample n) ω)
      atTop (𝓝 (terminalSum g θ M A ω)) :=
    ae_of_all _ fun ω => (stepSum_tendsto g θ M A ω).comp hsample
  have hQlim : ∀ᵐ ω ∂P, Tendsto (fun n => stepBracket g θ A (sample n) ω)
      atTop (𝓝 (gridVariance g θ)) := by
    filter_upwards [hc, hm, hz, hinf] with ω hcω hmω hzω hiω
    exact (stepBracket_tendsto g θ A ω hcω hmω hzω hiω).comp hsample
  simpa only [one_mul, one_pow] using
    KnightTerminalMGF.terminal_mgf_of_normalized_exponentials
      (fun n => stepSum g θ M A (sample n))
      (fun n => stepBracket g θ A (sample n))
      (terminalSum g θ M A) (gridVariance g θ) 1 hY hQ
      (fun n => ae_of_all _ fun ω => stepBracket_le_gridVariance g θ A (sample n) ω)
      hint hmean hYlim hQlim

/-- Joint Gaussian independence of the whole rectangular increment array.
All coefficients are tested in the same physical-time exponential identity;
separate scalar marginal identities would not imply this conclusion. -/
theorem rectangular_increment_independent_gaussian
    (g : IntervalGrid ι κ)
    (M : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0)
    (sample : ℕ → ℝ≥0) (hsample : Tendsto sample atTop atTop)
    (hc : ∀ᵐ ω ∂P, ∀ i, Continuous (fun t => A i t ω))
    (hm : ∀ᵐ ω ∂P, ∀ i, Monotone (fun t => A i t ω))
    (hz : ∀ᵐ ω ∂P, ∀ i, A i 0 ω = 0)
    (hinf : ∀ᵐ ω ∂P, ∀ j,
      (g.upper j : ℝ≥0∞) < terminalClock (fun t => A (g.channel j) t ω))
    (hinc : ∀ j, Measurable (fun ω =>
      rawChange M A (g.channel j) (g.upper j) ω -
        rawChange M A (g.channel j) (g.lower j) ω))
    (hY : ∀ θ n, AEStronglyMeasurable (stepSum g θ M A (sample n)) P)
    (hQ : ∀ θ n, AEStronglyMeasurable (stepBracket g θ A (sample n)) P)
    (hint : ∀ θ a n, Integrable (fun ω => Real.exp
      (a * stepSum g θ M A (sample n) ω -
        a ^ 2 * stepBracket g θ A (sample n) ω / 2)) P)
    (hmean : ∀ θ a n, (∫ ω, Real.exp
      (a * stepSum g θ M A (sample n) ω -
        a ^ 2 * stepBracket g θ A (sample n) ω / 2) ∂P) = 1) :
    iIndepFun (fun j ω => rawChange M A (g.channel j) (g.upper j) ω -
        rawChange M A (g.channel j) (g.lower j) ω) P ∧
      ∀ j, HasLaw (fun ω => rawChange M A (g.channel j) (g.upper j) ω -
        rawChange M A (g.channel j) (g.lower j) ω)
          (gaussianReal 0 (g.upper j - g.lower j)) P := by
  apply independent_gaussian_family_of_mgf hinc
  intro θ
  have h := (rectangular_increment_mgf g θ M A sample hsample hc hm hz hinf
    (hY θ) (hQ θ) (hint θ) (hmean θ)).2
  have hdiff : ∀ j, ((g.upper j - g.lower j : ℝ≥0) : ℝ) =
      (g.upper j : ℝ) - (g.lower j : ℝ) :=
    fun j => NNReal.coe_sub (g.ordered j)
  simp_rw [hdiff]
  simpa only [terminalSum, gridVariance, Finset.sum_div] using h

end

end Ripple.Stochastic.Knight
