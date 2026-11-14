import Ripple.Stochastic.CompletedKnight
import Ripple.Stochastic.KnightHalfLineExponential
import Ripple.Stochastic.KnightIntegralBracketFlat
import Ripple.Stochastic.KnightMeasurability

/-!
# Completed Knight theorem for the actual bounded channel integrals

All stochastic premises of the path-law completion theorem are produced from
the original bounded continuous adapted integrands: safe stopped exponential
normalization, fibre constancy, finite-clock convergence, and measurability.
The filtration is explicitly right continuous and contains ambient null sets.
The Brownian driver has a jointly independent fresh increment vector.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Ripple.Stochastic.Knight
open Ripple.Analysis Ripple.ProbabilityTheory
open FilteredItoIntegralL2 FilteredItoIntegralCLM ContinuousItoConsistency
open ContinuousItoHalfLineLinear ContinuousAdaptedIntegrand KnightIntegralConvergence
open KnightIntegralBracketFlat ClockStoppedIntegral

variable {Ω Ω₀ : Type} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ω₀]
  {P : Measure Ω} {P₀ : Measure Ω₀}
  [IsProbabilityMeasure P] [IsProbabilityMeasure P₀]
  {F : Filtration ℝ≥0 mΩ} {d : ℕ}

/-- The completed time change of the installed half-line integrals, with the
terminal values fixed by the measurable integer-time limit construction. -/
def integralKnightTimeChange
    (B : Fin d → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsFilteredPreBrownian (B i) F P)
    (hBc : ∀ i ω, Continuous (fun t => B i t ω)) (hBm : ∀ i t, Measurable (B i t))
    (H : Fin d → ℝ≥0 → Ω → ℝ)
    (hH : ∀ i (n : ℕ), MemLp (Function.uncurry (H i)) 2
      (trimMeasure_T (𝓖 := F) (μ := P) (n : ℝ≥0) (hBm i)))
    (A : Fin d → ℝ≥0 → Ω → ℝ≥0) (W : Fin d → ℝ≥0 → Ω₀ → ℝ) :
    Fin d → ℝ≥0 → Ω × Ω₀ → ℝ :=
  completedKnightTimeChange (channelHalfLineIto B hB hBc hBm H hH) A
    (fun i => knightTerminalValue (channelHalfLineIto B hB hBc hBm H hH i)) W

/-- Independent standard Brownian completion and exact reconstruction of the
actual integrals. There are no assumed stopping identities, flatness facts,
terminal-convergence facts, Gaussian laws for the result, or normalized
exponential identities among the hypotheses. -/
theorem completed_knight_integral
    (B : Fin d → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsFilteredPreBrownian (B i) F P)
    (hcoord : ∀ r t : ℝ≥0, r ≤ t → iIndepFun (fun i ω => B i t ω - B i r ω) P)
    (hpast : ∀ r t : ℝ≥0, r ≤ t →
      Indep (MeasurableSpace.comap (fun ω i => B i t ω - B i r ω) inferInstance) (F r) P)
    (hBc : ∀ i ω, Continuous (fun t => B i t ω)) (hBm : ∀ i t, Measurable (B i t))
    (hnull : ∀ t S, MeasurableSet S → P S = 0 → MeasurableSet[F t] S)
    [F.IsRightContinuous]
    (H : Fin d → ℝ≥0 → Ω → ℝ) (hHa : ∀ i t, Measurable[F t] (H i t))
    (hHc : ∀ i ω, Continuous (fun t => H i t ω))
    {K : ℝ} (hK : 0 ≤ K) (hHb : ∀ i t ω, |H i t ω| ≤ K)
    (hH : ∀ i (n : ℕ), MemLp (Function.uncurry (H i)) 2
      (trimMeasure_T (𝓖 := F) (μ := P) (n : ℝ≥0) (hBm i)))
    (A : Fin d → ℝ≥0 → Ω → ℝ≥0) (hAa : ∀ i, Adapted F (A i))
    (hAc : ∀ i ω, Continuous (fun t => A i t ω))
    (hAm : ∀ i ω, Monotone (fun t => A i t ω)) (hAz : ∀ i ω, A i 0 ω = 0)
    (hclock : ∀ i ω t,
      (∫ r in Ioc 0 t, (H i r ω) ^ 2 ∂timeMeasure) = (A i t ω : ℝ))
    (W : Fin d → ℝ≥0 → Ω₀ → ℝ)
    (hW : ∀ i, IsPreBrownian (W i) P₀)
    (hWind : iIndepFun (fun i z t => W i t z) P₀)
    (hWzero : ∀ i z, W i 0 z = 0)
    (hWjoint : ∀ i, Measurable (Function.uncurry (W i)))
    (hWcont : ∀ i, ∀ᵐ z ∂P₀, Continuous (fun t => W i t z)) :
    let β := integralKnightTimeChange B hB hBc hBm H hH A W
    (∀ i u, Measurable (β i u)) ∧
    (∀ i, IsPreBrownian (β i) (P.prod P₀)) ∧
    (∀ i, ∀ᵐ p ∂P.prod P₀, Continuous (fun u => β i u p)) ∧
    iIndepFun (fun i p u => β i u p) (P.prod P₀) ∧
    (∀ᵐ p ∂P.prod P₀, ∀ i t,
      channelHalfLineIto B hB hBc hBm H hH i t p.1 = β i (A i t p.1) p) := by
  let M := channelHalfLineIto B hB hBc hBm H hH
  let L := fun i => knightTerminalValue (M i)
  have hMj : ∀ i, Measurable (Function.uncurry (M i)) := by
    intro i
    letI := hB i
    exact measurable_uncurry_halfLineIto (hBc i) (hBm i) (Function.uncurry (H i)) (hH i)
  have hMc : ∀ i, ∀ᵐ ω ∂P, Continuous (fun t => M i t ω) := by
    intro i
    letI := hB i
    exact halfLineIto_ae_continuous (hBc i) (hBm i) (Function.uncurry (H i)) (hH i)
  have hMz : ∀ i, ∀ᵐ ω ∂P, M i 0 ω = 0 := by
    intro i
    letI := hB i
    filter_upwards [halfLineIto_finite_agreement (hBc i) (hBm i)
      (Function.uncurry (H i)) (hH i) 0,
      continuousIto_zero_ae 0 (hBc i) (hBm i)
        (finiteIntegrand (hBm i) (Function.uncurry (H i)) (hH i) 0)] with ω he hz
    exact (he ⟨0, zero_le, le_rfl⟩).trans hz
  have hpath : ∀ i ω r, IntegrableOn (fun s => (H i s ω) ^ 2) (Ioc 0 r) timeMeasure := by
    intro i ω r
    exact (((hHc i ω).pow 2).continuousOn.integrableOn_compact isCompact_Icc).mono_set
      (fun _ h => ⟨h.1.le, h.2⟩)
  have hflat : ∀ i, ∀ᵐ ω ∂P, ConstantOnClockFibres
      (fun t => A i t ω) (fun t => M i t ω) := by
    intro i
    letI := hB i
    exact halfLineIto_ae_constantOnClockFibres (hBc i) (hBm i) (A i) (hAa i)
      (hAc i) (hAm i) (Function.uncurry (H i))
      (stronglyMeasurable_uncurry (hHa i) (hHc i)) (hH i) (hpath i) (hclock i)
  have hlim : ∀ i, Measurable (L i) ∧ ∀ᵐ ω ∂P,
      terminalClock (fun t => A i t ω) ≠ ⊤ → Tendsto (fun t => M i t ω) atTop (𝓝 (L i ω)) := by
    intro i
    letI := hB i
    exact ae_finite_clock_halfLineIto_convergence (hBc i) (hBm i) hnull (A i)
      (hAa i) (hAc i) (hAm i) (hAz i) (Function.uncurry (H i))
      (stronglyMeasurable_uncurry (hHa i) (hHc i)) (hH i) (hclock i)
  exact completed_knight_of_terminal_normalization M A L W hW hWind hWzero hWjoint hWcont
    (fun i => ae_of_all _ (hAc i)) (fun i => ae_of_all _ (hAm i))
    (fun i => ae_of_all _ (hAz i)) hMc hMz hflat (fun i => (hlim i).2)
    (fun i => measurable_terminalClock (fun t => (hAa i t).mono (F.le t) le_rfl) (hAm i))
    (fun i u => measurable_terminalOriginalPath (hMj i) (hAa i) (hAc i) (hAm i)
      (hAz i) (hlim i).1 u)
    (fun κ _ g θ => halfLine_clock_step_terminal_normalization B hB hcoord hpast hBc hBm
      hnull H hHa hHc hK hHb hH A hAa hAc hAm hAz hclock g θ)

end Ripple.Stochastic.Knight
