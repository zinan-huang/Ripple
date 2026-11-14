-- Ripple/PopulationProtocol/ExactMajority/Probability/LateMixedFiveSixWindowTailClosed.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateMixedFiveSixWindowTailWf
import Ripple.PopulationProtocol.ExactMajority.Probability.AdvanceRegimeDispatchFive

/-!
# Mixed Phase-5/6 window tail with no `hdisp` and no `hdet`

`LateMixedFiveSixWindowTailWf` keeps `AdvanceRegimeDispatch 5` as a hypothesis.
It is now a theorem (`AdvanceNoOvershoot.advanceRegimeDispatch_five`), so the
public tail statements below carry neither it nor the false global overshoot
bridge.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateMixedFiveSixWindowTailClosed

open TimeTheorem
open LateMixedFiveSixWindow
open LateMixedFiveSixWindowTailWf

variable {n : ℕ}

theorem phaseSix_timer_kernel_tail_closed
    (init : InputCfg n)
    (hn : timePopulationThreshold ≤ n)
    (hvalid : validInitial init)
    (c : InputCfg n)
    (hreach :
      (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable
        init c)
    (hlower : ∀ a ∈ c, 2 ≤ a.phase.val)
    (hseed : PhaseSixTimerSeed n c) :
    ((NonuniformMajority
        (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel ^
          StageEventSpec.activationHorizon n) c
      {d | ¬ AdvanceNoOvershoot.NoOvershoot
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) 5 d} ≤
      ENNReal.ofReal (9 / (n : ℝ) ^ 3) :=
  phaseSix_timer_kernel_tail init hn hvalid
    AdvanceNoOvershoot.advanceRegimeDispatch_five c hreach hlower hseed

theorem law_phaseSixTimerFailure_tail_closed
    (init : InputCfg n)
    (hn : timePopulationThreshold ≤ n)
    (hvalid : validInitial init) :
    law init (phaseSixTimerFailure init) ≤
      ENNReal.ofReal (9 / (n : ℝ) ^ 3) :=
  law_phaseSixTimerFailure_tail init hn hvalid
    AdvanceNoOvershoot.advanceRegimeDispatch_five

theorem law_mixedFailure_raw_tail_closed
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (seedFailure : Set (InputLog n))
    (hseedProducer : PhaseSixSeedProducer init seedFailure) :
    law init (mixedFailure init) ≤
      (ENNReal.ofReal (1 / (n : ℝ) ^ 5) +
        ENNReal.ofReal (2 / (n : ℝ) ^ 5)) +
          ENNReal.ofReal (9 / (n : ℝ) ^ 3) :=
  law_mixedFailure_raw_tail init hinput seedFailure hseedProducer
    AdvanceNoOvershoot.advanceRegimeDispatch_five

/-- Original-law inverse-square tail for `mixedFailure`: the only inputs are
`GoodInput` and the Phase-6 seed producer. -/
theorem law_mixedFailure_inverse_square
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (seedFailure : Set (InputLog n))
    (hseedProducer : PhaseSixSeedProducer init seedFailure) :
    law init (mixedFailure init) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 2) :=
  LateMixedFiveSixWindowTailWf.law_mixedFailure_inverse_square
    init hinput seedFailure hseedProducer
    AdvanceNoOvershoot.advanceRegimeDispatch_five

end Ripple.PopulationProtocol.ExactMajority.LateMixedFiveSixWindowTailClosed

end
