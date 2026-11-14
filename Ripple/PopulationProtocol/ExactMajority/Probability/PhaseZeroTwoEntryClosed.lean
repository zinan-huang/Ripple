import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseZeroTwoEntry
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseZeroEntryProducer

/-!
# Phase 0-2 entry, unconditional (DOTY-LEAN-PLAN N11)

`PhaseZeroTwoEntry.phase_zero_two_entry_estimate` takes the Phase-0 entry estimate as a
hypothesis; `PhaseZeroEntryProducer.phase_zero_entry_estimate` proves it. This file
composes the two.
-/

open MeasureTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseZeroTwoEntryClosed

open TimeTheorem

/-- DOTY-LEAN-PLAN N11: from a good input, the reviewed Phase 0-2 entry stage fails with
probability at most `2 / n ^ 2`. -/
theorem phase_zero_two_entry_estimate {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (phaseEntryFailure (StageEventSpec.reviewedStageEvents n init)) ≤
      ENNReal.ofReal (2 / (n : ℝ) ^ 2) :=
  PhaseZeroTwoEntry.phase_zero_two_entry_estimate init hinput
    (PhaseZeroEntryProducer.phase_zero_entry_estimate init hinput)

end Ripple.PopulationProtocol.ExactMajority.PhaseZeroTwoEntryClosed
