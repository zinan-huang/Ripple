import Ripple.Stochastic.KnightTimeChangePaths
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Reconstruction on the product extension

The completed time change is the inverse-clock path up to its terminal clock,
then the terminal martingale value plus an auxiliary path. The reconstruction
identity holds on one full-measure set for every channel and every physical
time. This does not assert a Brownian law for the completed process.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace Ripple.ProbabilityTheory

open Ripple.Analysis

variable {ι Ω Ω₀ : Type*}

/-- Formula for the completed finite-family time change. The terminal values
are explicit inputs until finite-bracket convergence has constructed them. -/
noncomputable def completedKnightTimeChange
    (M : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0)
    (terminalValue : ι → Ω → ℝ) (W : ι → ℝ≥0 → Ω₀ → ℝ)
    (i : ι) (u : ℝ≥0) (ω : Ω × Ω₀) : ℝ :=
  completedTimeChangePath (fun t => M i t ω.1) (fun t => A i t ω.1)
    (terminalValue i ω.1) (fun t => W i t ω.2) u

variable [MeasurableSpace Ω] [MeasurableSpace Ω₀]
    {P : Measure Ω} {P₀ : Measure Ω₀}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P₀] [Fintype ι]

/-- Fibre constancy is already simultaneous in all times, so it can be
evaluated at arbitrary random times. No fixed-time exceptional-set argument
or stopping-time regularity is needed for this transfer. -/
theorem eq_at_randomTimes_of_clock_eq
    {M : ℝ≥0 → Ω → ℝ} {A : ℝ≥0 → Ω → ℝ≥0}
    (hflat : ∀ᵐ ω ∂P, ConstantOnClockFibres (fun t => A t ω) (fun t => M t ω))
    (σ ρ : Ω → ℝ≥0) (heq : ∀ᵐ ω ∂P, A (σ ω) ω = A (ρ ω) ω) :
    (fun ω => M (σ ω) ω) =ᵐ[P] (fun ω => M (ρ ω) ω) := by
  filter_upwards [hflat, heq] with ω hf he
  exact hf (σ ω) (ρ ω) he

/-- The completed time change reconstructs the original martingale paths.
The stochastic producers still have to provide fibre constancy and terminal
convergence. Independence or a Brownian conclusion is not carried as a premise. -/
theorem completedKnightTimeChange_comp
    (M : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0)
    (terminalValue : ι → Ω → ℝ) (W : ι → ℝ≥0 → Ω₀ → ℝ)
    (hc : ∀ i, ∀ᵐ ω ∂P, Continuous (fun t => A i t ω))
    (hm : ∀ i, ∀ᵐ ω ∂P, Monotone (fun t => A i t ω))
    (hz : ∀ i, ∀ᵐ ω ∂P, A i 0 ω = 0)
    (hflat : ∀ i, ∀ᵐ ω ∂P,
      ConstantOnClockFibres (fun t => A i t ω) (fun t => M i t ω))
    (hlim : ∀ i, ∀ᵐ ω ∂P, terminalClock (fun t => A i t ω) ≠ ⊤ →
      Tendsto (fun t => M i t ω) atTop (𝓝 (terminalValue i ω)))
    (hW : ∀ i, ∀ᵐ ω ∂P₀, W i 0 ω = 0) :
    ∀ᵐ ω ∂P.prod P₀, ∀ i t,
      completedKnightTimeChange M A terminalValue W i (A i t ω.1) ω = M i t ω.1 := by
  have hbase : ∀ᵐ ω ∂P, ∀ i,
      Continuous (fun t => A i t ω) ∧ Monotone (fun t => A i t ω) ∧
      A i 0 ω = 0 ∧ ConstantOnClockFibres (fun t => A i t ω) (fun t => M i t ω) ∧
      (terminalClock (fun t => A i t ω) ≠ ⊤ →
        Tendsto (fun t => M i t ω) atTop (𝓝 (terminalValue i ω))) := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [hc i, hm i, hz i, hflat i, hlim i] with ω hcω hmω hzω hfω hlω
    exact ⟨hcω, hmω, hzω, hfω, hlω⟩
  have haux : ∀ᵐ ω ∂P₀, ∀ i, W i 0 ω = 0 := ae_all_iff.mpr hW
  have hf : MeasurePreserving (Prod.fst : Ω × Ω₀ → Ω) (P.prod P₀) P :=
    measurePreserving_fst
  have hs : MeasurePreserving (Prod.snd : Ω × Ω₀ → Ω₀) (P.prod P₀) P₀ :=
    measurePreserving_snd
  filter_upwards [hf.quasiMeasurePreserving.ae hbase,
    hs.quasiMeasurePreserving.ae haux] with ω hb hw
  intro i t
  obtain ⟨hcω, hmω, hzω, hfω, hlω⟩ := hb i
  exact completedTimeChangePath_comp hcω hmω hzω hfω hlω (hw i) t

end Ripple.ProbabilityTheory
