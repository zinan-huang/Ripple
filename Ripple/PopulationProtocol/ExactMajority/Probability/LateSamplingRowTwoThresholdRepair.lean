-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingRowTwoThresholdRepair.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateThresholdAcceptedTrialSlot
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingRowTwoChoices

/-!
# Row-two original-law wrapper for the threshold-aware zero slot
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingRowTwoThresholdRepair

open TimeTheorem PairLog
open LateSamplingRowTwoChoices
open LateAcceptedTrialSlot
open LateThresholdAcceptedTrialSlot

variable {n : ℕ}

/-- Drop-in replacement for `LateSamplingRowTwoChoices.rowTwoFailure`. -/
def rowTwoThresholdFailure
    (init : InputCfg n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (H : ℕ) : Set (InputLog n) :=
  originalPrerequisiteWithThresholdAcceptedFailure init
    (rowTwoClassChoice ell hell)
    (rowTwoIndexChoice init ell hell)
    (constantHorizonChoice init H)

/-- Unconditioned original-law charge for the repaired row-two family. -/
theorem law_rowTwoThresholdFailure_tail
    (init : InputCfg n) (hcard : init.card = n)
    (hn : timePopulationThreshold ≤ n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (H : ℕ) :
    law init (rowTwoThresholdFailure init ell hell H) ≤
      ENNReal.ofReal
        (13 * (n : ℝ) ^ 2 *
          Real.exp (-(n : ℝ) / 800000000000000)) := by
  exact law_prerequisites_withThresholdAccepted_tail init hcard hn
    (rowTwoClassChoice ell hell)
    (rowTwoIndexChoice init ell hell)
    (constantHorizonChoice init H)

/-- Inverse-power form of the same repaired original-law estimate. -/
theorem law_rowTwoThresholdFailure_inverse_power
    (init : InputCfg n) (hcard : init.card = n)
    (hn : timePopulationThreshold ≤ n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (H : ℕ) :
    law init (rowTwoThresholdFailure init ell hell H) ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-190)) := by
  exact law_prerequisites_withThresholdAccepted_inverse_power init hcard hn
    (rowTwoClassChoice ell hell)
    (rowTwoIndexChoice init ell hell)
    (constantHorizonChoice init H)

/-!
THEOREM LIST
* `law_rowTwoThresholdFailure_tail`
* `law_rowTwoThresholdFailure_inverse_power`

CLOSES
* A new-file-only replacement for the old row-two original-law failure family.
* Preservation of the exact stopping-line and finite-union probability charge.

UNFINISHED
* Construct the deterministic four-inequality class cover using
  `threshold_zero_slot_cover`.
* Produce the timer-selected constant horizon and its legal-prefix receipt.
* Handle the protected-class sentinel boundary `ell + 2 = L` separately.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateSamplingRowTwoThresholdRepair

end
