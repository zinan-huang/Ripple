-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingMainAssembly.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingFinalNumerics
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMainAssembly

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.AveragingMainAssembly

open TimeTheorem StageEventSpec
open AveragingSparseEntry AveragingEventInterface
open AveragingGlobalFailureSplice AveragingFinalNumerics AveragingObservedHourTails
open PhaseThreeClockRows PhaseThreeClockRowsGuarded

/-- N13 with the one named N12 hypothesis requested by the plan.  N12 is used
 only here; all local N13 estimates are under the original path law. -/
theorem averaging_estimate_of_asynchronous_clock
    {n : ℕ} (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (asynchronous_clock_estimate :
      law init (phaseClockFailure (reviewedStageEvents n init)) ≤
        ENNReal.ofReal (8 / (n : ℝ) ^ 5)) :
    law init (phaseAveragingFailure (reviewedStageEvents n init)) ≤
      ENNReal.ofReal (3 / (n : ℝ) ^ 2) := by
  have hn : timePopulationThreshold ≤ n := hinput.1
  have hvalid : validInitial init := hinput.2.1
  have hcard : init.card = n := hinput.2.2
  have hsparse := averaging_sparse_entry_exception init hinput
  have hsafe := uniform_safe_seed_averaging init hvalid hcard hn
  have hcover : phaseAveragingFailure (reviewedStageEvents n init) ⊆
      phaseClockFailure (reviewedStageEvents n init) ∪
        (phaseAveragingFailure (reviewedStageEvents n init) \
          safeSparseEntry init) ∪
        (phaseAveragingFailure (reviewedStageEvents n init) ∩
          safeSparseEntry init) := by
    intro ω hω
    by_cases hc : ω ∈ phaseClockFailure (reviewedStageEvents n init)
    · exact Or.inl (Or.inl hc)
    · by_cases hs : ω ∈ safeSparseEntry init
      · exact Or.inr ⟨hω, hs⟩
      · exact Or.inl (Or.inr ⟨hω, hs⟩)
  calc
    law init (phaseAveragingFailure (reviewedStageEvents n init)) ≤
        law init (phaseClockFailure (reviewedStageEvents n init) ∪
          (phaseAveragingFailure (reviewedStageEvents n init) \
            safeSparseEntry init) ∪
          (phaseAveragingFailure (reviewedStageEvents n init) ∩
            safeSparseEntry init)) := measure_mono hcover
    _ ≤ law init (phaseClockFailure (reviewedStageEvents n init)) +
        law init (phaseAveragingFailure (reviewedStageEvents n init) \
          safeSparseEntry init) +
        law init (phaseAveragingFailure (reviewedStageEvents n init) ∩
          safeSparseEntry init) := by
      exact (measure_union_le _ _).trans
        (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (8 / (n : ℝ) ^ 5) +
        ENNReal.ofReal (2 / (n : ℝ) ^ 2) +
        (5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ≥0∞) * hourError n +
          2 * hourError n + ENNReal.ofReal (1 / (n : ℝ) ^ 4)) :=
      add_le_add (add_le_add asynchronous_clock_estimate hsparse) hsafe
    _ ≤ ENNReal.ofReal (3 / (n : ℝ) ^ 2) := by
      refine le_trans (le_of_eq ?_) (averaging_complete_error_budget hn)
      ring

/-- The N13 estimate from the step-three rows and the guarded Main row. The plan-typed headline is `AveragingFinal.averaging_estimate`. -/
theorem averaging_estimate_of_main_rows
    {n : ℕ} (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (hrows : PhaseThreeClockMainAssembly.StepThreeRows init)
    (hmain : law init
      (PhaseThreeClockRowsGuarded.guardedFailure init
        (PhaseThreeClockRowsGuarded.guardMain init)
        (PhaseThreeClockRows.mainRow init)) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 29)) :
    law init (phaseAveragingFailure (reviewedStageEvents n init)) ≤
      ENNReal.ofReal (3 / (n : ℝ) ^ 2) := by
  apply averaging_estimate_of_asynchronous_clock init hinput
  exact PhaseThreeClockMainAssembly.asynchronous_clock_estimate_of_four_rows
    init hinput hrows hmain

end Ripple.PopulationProtocol.ExactMajority.AveragingMainAssembly

end
