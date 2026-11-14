import Ripple.PopulationProtocol.ExactMajority.Probability.LateSmallGapComposition
import Ripple.PopulationProtocol.ExactMajority.Probability.PairLog
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseZeroTwoEntryClosed
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMainFinal
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingFinal
import Ripple.PopulationProtocol.ExactMajority.Probability.StrongContinuation
import Ripple.PopulationProtocol.ExactMajority.Probability.TieContinuation
import Ripple.PopulationProtocol.ExactMajority.Probability.UniformRecovery

/-!
# Doty's stabilization-time theorem

The reviewed stage events and the fixed small-gap late estimate supply every
probability estimate of the stabilization-time assembly.
-/

namespace Ripple.PopulationProtocol.ExactMajority.DotyStabilizationTime

open TimeTheorem StageEventSpec

/-- Doty's population-uniform high-probability and expected stabilization bounds. -/
theorem doty_stabilization_time : TimeTheorem.DotyTimeClaim :=
  dotyTimeClaim_of_estimates StageEventSpec.reviewedStageEvents
    (fun n hn init hv hc =>
      PhaseZeroTwoEntryClosed.phase_zero_two_entry_estimate init ⟨hn, hv, hc⟩)
    (fun n hn init hv hc =>
      PhaseThreeClockMainFinal.asynchronous_clock_estimate init ⟨hn, hv, hc⟩)
    (fun n hn init hv hc =>
      AveragingFinal.averaging_estimate init ⟨hn, hv, hc⟩)
    (fun n hn init hv hc =>
      LateSmallGapComposition.smallGap_late_estimate init ⟨hn, hv, hc⟩)
    (fun n hn init hv hc =>
      StrongContinuation.strong_continuation_estimate init ⟨hn, hv, hc⟩)
    (fun n hn init hv hc =>
      TieContinuation.tie_continuation_estimate init ⟨hn, hv, hc⟩)
    (fun n hn init hv hc b hr hnot =>
      UniformRecovery.reachable_recovery_estimate init ⟨hn, hv, hc⟩ b hr hnot)
    (fun n hn init hv hc => PairLog.pathwiseRecoverySplit init)

end Ripple.PopulationProtocol.ExactMajority.DotyStabilizationTime
