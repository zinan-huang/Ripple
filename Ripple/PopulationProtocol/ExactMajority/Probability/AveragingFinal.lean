-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingFinal.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingMainAssembly
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMainFinal

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.AveragingFinal

open TimeTheorem StageEventSpec

/-- N13 in the exact type of `DOTY-LEAN-PLAN`: the N12 hypothesis of
`AveragingMainAssembly.averaging_estimate_of_asynchronous_clock` is discharged
by `PhaseThreeClockMainFinal.asynchronous_clock_estimate`. -/
theorem averaging_estimate
    {n : ℕ} (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (phaseAveragingFailure (reviewedStageEvents n init)) ≤
      ENNReal.ofReal (3 / (n : ℝ) ^ 2) :=
  AveragingMainAssembly.averaging_estimate_of_asynchronous_clock init hinput
    (PhaseThreeClockMainFinal.asynchronous_clock_estimate init hinput)

end Ripple.PopulationProtocol.ExactMajority.AveragingFinal

end
