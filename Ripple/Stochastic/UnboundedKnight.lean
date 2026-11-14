import Ripple.Stochastic.KnightBrownianLaw
import Ripple.Stochastic.KnightTimeChangeContinuity

/-!
# The unbounded-clock Knight theorem

The stochastic input is normalization of the actual common-physical-time
rectangular exponentials. This module derives the rectangular increment laws,
the Brownian finite-dimensional laws, independence of whole channel paths,
continuity, and reconstruction. Supplying the normalization fields for the
installed stochastic integral is a separate integral/exponential theorem.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Ripple.Stochastic.Knight

open Ripple.Analysis Ripple.ProbabilityTheory

variable {ι Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- The common-time exponential identities needed by the rectangular-grid
argument. The same grid and coefficients are used in the sum and bracket;
there is no independence premise and no Brownian conclusion among the fields. -/
structure NormalizedGridExponentials
    (M : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0)
    (sample : ℕ → ℝ≥0) (P : Measure Ω) : Prop where
  sum_measurable : ∀ (κ : Type) [Fintype κ] (g : IntervalGrid ι κ)
    (θ : κ → ℝ) (n : ℕ), AEStronglyMeasurable (stepSum g θ M A (sample n)) P
  bracket_measurable : ∀ (κ : Type) [Fintype κ] (g : IntervalGrid ι κ)
    (θ : κ → ℝ) (n : ℕ), AEStronglyMeasurable (stepBracket g θ A (sample n)) P
  exp_integrable : ∀ (κ : Type) [Fintype κ] (g : IntervalGrid ι κ)
    (θ : κ → ℝ) (a : ℝ) (n : ℕ), Integrable (fun ω => Real.exp
      (a * stepSum g θ M A (sample n) ω -
        a ^ 2 * stepBracket g θ A (sample n) ω / 2)) P
  exp_mean : ∀ (κ : Type) [Fintype κ] (g : IntervalGrid ι κ)
    (θ : κ → ℝ) (a : ℝ) (n : ℕ), (∫ ω, Real.exp
      (a * stepSum g θ M A (sample n) ω -
        a ^ 2 * stepBracket g θ A (sample n) ω / 2) ∂P) = 1

variable [IsProbabilityMeasure P]

/-- Normalized common-time exponentials give all rectangular Gaussian
increment laws when every channel clock is unbounded. -/
theorem rectangularGaussian_of_normalized_exponentials
    (M : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0)
    (sample : ℕ → ℝ≥0) (hsample : Tendsto sample atTop atTop)
    (hc : ∀ᵐ ω ∂P, ∀ i, Continuous (fun t => A i t ω))
    (hm : ∀ᵐ ω ∂P, ∀ i, Monotone (fun t => A i t ω))
    (hz : ∀ᵐ ω ∂P, ∀ i, A i 0 ω = 0)
    (htop : ∀ᵐ ω ∂P, ∀ i, terminalClock (fun t => A i t ω) = ⊤)
    (hraw : ∀ i u, Measurable (rawChange M A i u))
    (hexp : NormalizedGridExponentials M A sample P) :
    HasRectangularGaussianIncrements (rawChange M A) P := by
  intro κ _ g
  apply rectangular_increment_independent_gaussian g M A sample hsample hc hm hz
  · filter_upwards [htop] with ω hω
    intro j
    rw [hω (g.channel j)]
    exact ENNReal.coe_lt_top
  · intro j
    exact (hraw _ _).sub (hraw _ _)
  · exact hexp.sum_measurable κ g
  · exact hexp.bracket_measurable κ g
  · exact hexp.exp_integrable κ g
  · exact hexp.exp_mean κ g

/-- With unbounded clocks, fibre constancy transports the original zero
initial value through the possibly discontinuous strict inverse. -/
theorem rawChange_zero_of_unbounded
    {M : ι → ℝ≥0 → Ω → ℝ} {A : ι → ℝ≥0 → Ω → ℝ≥0}
    (hc : ∀ᵐ ω ∂P, ∀ i, Continuous (fun t => A i t ω))
    (hm : ∀ᵐ ω ∂P, ∀ i, Monotone (fun t => A i t ω))
    (hz : ∀ᵐ ω ∂P, ∀ i, A i 0 ω = 0)
    (hMzero : ∀ᵐ ω ∂P, ∀ i, M i 0 ω = 0)
    (hflat : ∀ᵐ ω ∂P, ∀ i,
      ConstantOnClockFibres (fun t => A i t ω) (fun t => M i t ω))
    (htop : ∀ᵐ ω ∂P, ∀ i, terminalClock (fun t => A i t ω) = ⊤) :
    ∀ i, ∀ᵐ ω ∂P, rawChange M A i 0 ω = 0 := by
  intro i
  filter_upwards [hc, hm, hz, hMzero, hflat, htop] with ω hcω hmω hzω hMω hfω htω
  have h := rawTimeChangePath_comp_of_terminal_eq_top
    (hcω i) (hmω i) (hzω i) (hfω i) (htω i) 0
  simpa only [hzω i, hMω i] using h

/-- Fibre collapse gives continuous raw paths at every finite internal time
under an unbounded clock. No continuity of the strict inverse is assumed. -/
theorem rawChange_continuous_of_unbounded
    {M : ι → ℝ≥0 → Ω → ℝ} {A : ι → ℝ≥0 → Ω → ℝ≥0}
    (hc : ∀ᵐ ω ∂P, ∀ i, Continuous (fun t => A i t ω))
    (hm : ∀ᵐ ω ∂P, ∀ i, Monotone (fun t => A i t ω))
    (hz : ∀ᵐ ω ∂P, ∀ i, A i 0 ω = 0)
    (hMc : ∀ᵐ ω ∂P, ∀ i, Continuous (fun t => M i t ω))
    (hflat : ∀ᵐ ω ∂P, ∀ i,
      ConstantOnClockFibres (fun t => A i t ω) (fun t => M i t ω))
    (htop : ∀ᵐ ω ∂P, ∀ i, terminalClock (fun t => A i t ω) = ⊤) :
    ∀ᵐ ω ∂P, ∀ i, Continuous (fun u => rawChange M A i u ω) := by
  filter_upwards [hc, hm, hz, hMc, hflat, htop] with ω hcω hmω hzω hMω hfω htω
  intro i
  apply continuous_iff_continuousAt.mpr
  intro u
  apply continuousAt_rawTimeChangePath (hcω i) (hmω i) (hzω i) (hMω i) (hfω i)
  rw [htω i]
  exact ENNReal.coe_lt_top

/-- The unbounded-clock Knight conclusion, conditional only on explicitly
listed path, measurability, and common-time stochastic exponential inputs.
The path law and whole-channel independence conclusions are derived. -/
theorem unboundedKnight_of_normalized_exponentials
    (M : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0)
    (sample : ℕ → ℝ≥0) (hsample : Tendsto sample atTop atTop)
    (hc : ∀ᵐ ω ∂P, ∀ i, Continuous (fun t => A i t ω))
    (hm : ∀ᵐ ω ∂P, ∀ i, Monotone (fun t => A i t ω))
    (hz : ∀ᵐ ω ∂P, ∀ i, A i 0 ω = 0)
    (hMc : ∀ᵐ ω ∂P, ∀ i, Continuous (fun t => M i t ω))
    (hMzero : ∀ᵐ ω ∂P, ∀ i, M i 0 ω = 0)
    (hflat : ∀ᵐ ω ∂P, ∀ i,
      ConstantOnClockFibres (fun t => A i t ω) (fun t => M i t ω))
    (htop : ∀ᵐ ω ∂P, ∀ i, terminalClock (fun t => A i t ω) = ⊤)
    (hraw : ∀ i u, Measurable (rawChange M A i u))
    (hexp : NormalizedGridExponentials M A sample P) :
    (∀ i, IsPreBrownian (rawChange M A i) P) ∧
      iIndepFun (fun i ω u => rawChange M A i u ω) P ∧
      (∀ᵐ ω ∂P, ∀ i, Continuous (fun u => rawChange M A i u ω)) ∧
      (∀ᵐ ω ∂P, ∀ i t, M i t ω = rawChange M A i (A i t ω) ω) := by
  have hrect := rectangularGaussian_of_normalized_exponentials
    M A sample hsample hc hm hz htop hraw hexp
  have hzero := rawChange_zero_of_unbounded hc hm hz hMzero hflat htop
  obtain ⟨hlaw, hind⟩ := brownian_family_of_rectangular hrect hraw hzero
  refine ⟨hlaw, hind, rawChange_continuous_of_unbounded hc hm hz hMc hflat htop, ?_⟩
  filter_upwards [hc, hm, hz, hflat, htop] with ω hcω hmω hzω hfω htω
  intro i t
  exact (rawTimeChangePath_comp_of_terminal_eq_top
    (hcω i) (hmω i) (hzω i) (hfω i) (htω i) t).symm

end Ripple.Stochastic.Knight
