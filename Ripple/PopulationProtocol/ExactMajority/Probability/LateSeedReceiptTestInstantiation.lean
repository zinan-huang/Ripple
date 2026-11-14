-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSeedReceiptTestInstantiation.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedProtectedTestFailure
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedNearTestFailure

/-!
# Instantiating the two named N16 test-failure families

`LateSeedProtectedTestFailure` supplies `protectedTestFailure` and its original-law
estimate.  `LateSeedNearTestFailure` supplies `nearTestFailure` and its original-law estimate.  The deterministic
cover and the old-index family remain explicit inputs.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.LateStrengthening

open TimeTheorem

variable {n : ℕ}

/-- `late_sampling_seed_receipt_safe_estimate` with both test families and both
`1 / n^4` estimates instantiated. -/
theorem late_sampling_seed_receipt_safe_estimate_with_named_test_failures
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (oldIndexFailure : Set (InputLog n))
    (hcover :
      lateSamplingSeedProducerSafeFailure init ⊆
        protectedTestFailure init ∪
          (nearTestFailure init ∪ oldIndexFailure))
    (hold :
      law init oldIndexFailure ≤
        ENNReal.ofReal
          (Real.rpow (n : ℝ) (-(207 / 100 : ℝ)))) :
    law init (lateSamplingSeedProducerSafeFailure init) ≤
      ENNReal.ofReal
        (2 / (n : ℝ) ^ 4 +
          Real.rpow (n : ℝ) (-(207 / 100 : ℝ))) := by
  exact
    late_sampling_seed_receipt_safe_estimate init
      (protectedTestFailure init) (nearTestFailure init) oldIndexFailure
      hcover
      (protected_test_failure_estimate init hinput)
      (near_test_failure_estimate init hinput)
      hold

end Ripple.PopulationProtocol.ExactMajority.LateStrengthening

end
