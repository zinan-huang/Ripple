import Ripple.Stochastic.KnightStepExponential
import Ripple.Stochastic.ContinuousItoHalfLineLinear
import Ripple.Stochastic.KnightIntegralConvergence
import Ripple.Stochastic.KnightCompletedIncrementLaw

/-!
# Normalized exponentials for the actual half-line channel integrals

Finite-window normalization is transferred through simultaneous path
agreement before evaluation at the random stopping times. Finite-terminal-
clock convergence is supplied by the actual integral convergence theorem.
No normalized-exponential or terminal-convergence premise is left open.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Ripple.Stochastic.Knight
open Ripple.Analysis Ripple.ProbabilityTheory
open FilteredItoIntegralL2 FilteredItoIntegralCLM ContinuousItoConsistency
open ContinuousItoHalfLineLinear ContinuousAdaptedIntegrand KnightIntegralConvergence

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ} {d : ℕ}
  (B : Fin d → ℝ≥0 → Ω → ℝ)
  (hB : ∀ i, IsFilteredPreBrownian (B i) F P)

/-- The installed half-line integral in each channel, using its actual
integer-window predictable L² membership proofs. -/
def channelHalfLineIto
    (hBc : ∀ i ω, Continuous (fun t => B i t ω)) (hBm : ∀ i t, Measurable (B i t))
    (H : Fin d → ℝ≥0 → Ω → ℝ)
    (hH : ∀ i (n : ℕ), MemLp (Function.uncurry (H i)) 2
      (trimMeasure_T (𝓖 := F) (μ := P) (n : ℝ≥0) (hBm i)))
    (i : Fin d) : ℝ≥0 → Ω → ℝ := by
  letI := hB i
  exact halfLineIto (hBc i) (hBm i) (Function.uncurry (H i)) (hH i)

section Normalization
variable
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

include hcoord hpast hnull hHa hHc hK hHb hAa hAc hAm hAz hclock in
/-- The actual half-line integral supplies mean-one normalized exponentials
at every natural physical time, including on finite-terminal-clock paths. -/
theorem halfLine_clock_step_normalized_exponential {κ : Type} [Fintype κ]
    (g : IntervalGrid (Fin d) κ) (θ : κ → ℝ) (a : ℝ) (n : ℕ) :
    Integrable (fun ω => Real.exp
      (a * cappedStepSum g θ (channelHalfLineIto B hB hBc hBm H hH) A n ω -
        a ^ 2 * stepBracket g θ A n ω / 2)) P ∧
      (∫ ω, Real.exp
        (a * cappedStepSum g θ (channelHalfLineIto B hB hBc hBm H hH) A n ω -
          a ^ 2 * stepBracket g θ A n ω / 2) ∂P) = 1 := by
  have hagree : ∀ᵐ ω ∂P, ∀ i t, t ≤ (n : ℝ≥0) →
      channelHalfLineIto B hB hBc hBm H hH i t ω =
        channelItoOfFun B hB n hBc hBm H i t ω := by
    apply ae_all_iff.mpr
    intro i
    letI := hB i
    exact halfLineIto_eq_continuousItoOfFun (hBc i) (hBm i) (H i) (hH i) n (hH i n)
  have heq := cappedStepSum_congr_ae_on g θ
    (channelHalfLineIto B hB hBc hBm H hH) (channelItoOfFun B hB n hBc hBm H) A n hagree
  have hlocal := clock_step_normalized_exponential B hB hcoord hpast g θ n
    hBc hBm hnull H hHa hHc hK hHb A hAa hAc hAm hAz hclock a
    (⟨n, zero_le, le_rfl⟩ : Icc (0 : ℝ≥0) (n : ℝ≥0))
  have hexp : (fun ω => Real.exp
      (a * cappedStepSum g θ (channelHalfLineIto B hB hBc hBm H hH) A n ω -
        a ^ 2 * stepBracket g θ A n ω / 2)) =ᵐ[P]
      (fun ω => Real.exp
        (a * cappedStepSum g θ (channelItoOfFun B hB n hBc hBm H) A n ω -
          a ^ 2 * stepBracket g θ A n ω / 2)) := by
    filter_upwards [heq] with ω hω
    rw [hω n le_rfl]
  exact ⟨hlocal.1.congr hexp.symm, (integral_congr_ae hexp).trans hlocal.2⟩

include hcoord hpast hnull hHa hHc hK hHb hAa hAc hAm hAz hclock in
/-- All four measurable and normalized-exponential inputs to the random
terminal-bracket limit are supplied for the actual half-line integrals. -/
theorem halfLine_clock_step_exponential_premises {κ : Type} [Fintype κ]
    (g : IntervalGrid (Fin d) κ) (θ : κ → ℝ) :
    (∀ n : ℕ, AEStronglyMeasurable
      (cappedStepSum g θ (channelHalfLineIto B hB hBc hBm H hH) A n) P) ∧
    (∀ n : ℕ, AEStronglyMeasurable (stepBracket g θ A n) P) ∧
    (∀ a (n : ℕ), Integrable (fun ω => Real.exp
      (a * cappedStepSum g θ (channelHalfLineIto B hB hBc hBm H hH) A n ω -
        a ^ 2 * stepBracket g θ A n ω / 2)) P) ∧
    (∀ a (n : ℕ), (∫ ω, Real.exp
      (a * cappedStepSum g θ (channelHalfLineIto B hB hBc hBm H hH) A n ω -
        a ^ 2 * stepBracket g θ A n ω / 2) ∂P) = 1) := by
  have hn := halfLine_clock_step_normalized_exponential B hB hcoord hpast hBc hBm
    hnull H hHa hHc hK hHb hH A hAa hAc hAm hAz hclock g θ
  have hmeas (n : ℕ) := aestronglyMeasurable_of_opposite_exponentials
    (cappedStepSum g θ (channelHalfLineIto B hB hBc hBm H hH) A n)
    (stepBracket g θ A n)
    (by simpa only [one_mul, one_pow] using (hn 1 n).1)
    (by simpa only [neg_one_mul, neg_one_sq, one_mul] using (hn (-1) n).1)
  exact ⟨fun n => (hmeas n).1, fun n => (hmeas n).2,
    fun a n => (hn a n).1, fun a n => (hn a n).2⟩

include hcoord hpast hnull hHa hHc hK hHb hAa hAc hAm hAz hclock in
/-- The finite-terminal-clock contribution of the actual half-line integrals
has a mean-one normalized exponential. Both the normalization and terminal
path convergence are constructed from the original bounded integrands. -/
theorem halfLine_clock_step_terminal_normalization {κ : Type} [Fintype κ]
    (g : IntervalGrid (Fin d) κ) (θ : κ → ℝ) :
    Integrable (fun ω => Real.exp
      (originalGridSum g θ (channelHalfLineIto B hB hBc hBm H hH) A
          (fun i => knightTerminalValue (channelHalfLineIto B hB hBc hBm H hH i)) ω -
        terminalGridBracket g θ (fun i => terminalClock (fun t => A i t ω)) / 2)) P ∧
      (∫ ω, Real.exp
        (originalGridSum g θ (channelHalfLineIto B hB hBc hBm H hH) A
            (fun i => knightTerminalValue (channelHalfLineIto B hB hBc hBm H hH i)) ω -
          terminalGridBracket g θ (fun i => terminalClock (fun t => A i t ω)) / 2) ∂P) = 1 := by
  have hlim : ∀ᵐ ω ∂P, ∀ i, terminalClock (fun t => A i t ω) ≠ ⊤ →
      Tendsto (fun t => channelHalfLineIto B hB hBc hBm H hH i t ω) atTop
        (nhds (knightTerminalValue (channelHalfLineIto B hB hBc hBm H hH i) ω)) := by
    apply ae_all_iff.mpr
    intro i
    letI := hB i
    exact (ae_finite_clock_halfLineIto_convergence (hBc i) (hBm i) hnull (A i)
      (hAa i) (hAc i) (hAm i) (hAz i) (Function.uncurry (H i))
      (stronglyMeasurable_uncurry (hHa i) (hHc i)) (hH i) (hclock i)).2
  obtain ⟨hY, hQ, hint, hmean⟩ := halfLine_clock_step_exponential_premises
    B hB hcoord hpast hBc hBm hnull H hHa hHc hK hHb hH A hAa hAc hAm hAz hclock g θ
  exact capped_step_terminal_normalization g θ (channelHalfLineIto B hB hBc hBm H hH)
    A (fun i => knightTerminalValue (channelHalfLineIto B hB hBc hBm H hH i))
    (ae_of_all _ fun ω i => hAm i ω) hlim hY hQ hint hmean

end Normalization
end Ripple.Stochastic.Knight
