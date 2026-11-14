-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingCompletedFuelProtected.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingFixedRowTwoHorizon

/-!
# Completed row-two fuel with the fixed-horizon premise discharged
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingCompletedFuelProtected

open TimeTheorem
open LateTimerPrefixScalar
open LateSamplingSeedReceipt LateSamplingStrongSeedReceipt
open LateSamplingRowTwoThresholdRepair
open LateSamplingCompletedFuelSnapshot
open LateSamplingFixedRowTwoHorizon

variable {n : ℕ}

/-- All local original-law charges needed by the protected completed-fuel
consumer.  The upstream existence of `StrongSeedReceipt` and the N16 receipt
is intentionally not duplicated here. -/
def completedProtectedFuelFailure
    (init : InputCfg n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n) :
    Set (InputLog n) :=
  fixedRowTwoHorizonProductionFailure init ∪
    rowTwoThresholdFailure init ell hell (protectionHorizon n)

/-- Exact sum of all unconditional local charges from `GoodInput`. -/
theorem law_completedProtectedFuelFailure_inverse_power
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n) :
    law init (completedProtectedFuelFailure init ell hell) ≤
      ((ENNReal.ofReal
          (Real.rpow (n : ℝ) (-(103 / 50 : ℝ))) +
        (ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 3) +
          ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 3))) +
        ENNReal.ofReal
          (Real.rpow (n : ℝ) (-(6347 / 3125 : ℝ)))) +
      ENNReal.ofReal (Real.rpow (n : ℝ) (-190)) := by
  exact (measure_union_le _ _).trans
    (add_le_add
      (law_fixedRowTwoHorizonProductionFailure_tail init hinput)
      (law_rowTwoThresholdFailure_inverse_power
        init hinput.2.2 hinput.1 ell hell (protectionHorizon n)))

/-- The composed consumer.  Compared with
`twoLevelFuelLedger_of_completed_good_path`, the `FixedRowTwoHorizon`
hypothesis has disappeared; it is constructed from the guarded timer and the
two stopping-time spread complements. -/
theorem twoLevelFuelLedger_of_completed_protected_good_path
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n}
    {seed allThree four five completed M C R : ℕ}
    {Snapshot : InputCfg n → Prop}
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (sigma : Sign)
    (hstrong : StrongSeedReceipt init omega seed allThree four five completed
      M C R Snapshot)
    (hseed : LateSamplingSeedReceipt init M ell.val sigma
      (trace init omega four))
    (hgood : omega ∉ completedProtectedFuelFailure init ell hell) :
    Phase6FuelLedger.TwoLevelFuelLedger
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      ell (LatePotential.fuelFloor n) (trace init omega completed) := by
  have hproduction :
      omega ∉ fixedRowTwoHorizonProductionFailure init :=
    fun h => hgood (Or.inl h)
  have hrow :
      omega ∉ rowTwoThresholdFailure init ell hell
        (protectionHorizon n) :=
    fun h => hgood (Or.inr h)
  have hfixed :=
    fixedRowTwoHorizon_of_not_productionFailure
      hinput ell hell sigma hstrong hseed hproduction
  have hcompletedGood :
      omega ∉ completedRowTwoFuelFailure init ell hell
        (protectionHorizon n) := by
    rintro (hcompletion | hthreshold)
    · exact hproduction (Or.inr hcompletion)
    · exact hrow hthreshold
  exact twoLevelFuelLedger_of_completed_good_path
    hinput.2.1 hinput.1 ell hell sigma hstrong hseed
    hfixed hcompletedGood

/-!
THEOREM LIST
* `completedProtectedFuelFailure`
* `law_completedProtectedFuelFailure_inverse_power`
* `twoLevelFuelLedger_of_completed_protected_good_path`

CLOSES
* The named original-law union of guarded timer, both spreads, completion,
  and repaired row-two threshold failures.
* The exact sum of the five unconditional charges.
* The completed `TwoLevelFuelLedger` theorem with no
  `FixedRowTwoHorizon` hypothesis.

UNFINISHED
* Global production of the carried `StrongSeedReceipt` remains the existing
  `completionBase` seam.  This file does not pretend that
  `law_prefix_failure_zero` or `completionFailure` alone supplies it.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateSamplingCompletedFuelProtected

end
