-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSeedProtectedTestFailure.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedReceiptProducerTail
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingDominantLevelSplice

/-!
# Original-law protected-test charge for the retained-credit receipt

The N13 hour induction already supplies the required original-law event:
`AveragingDominantLevelSplice.globalHourFailure`.  Its proof uses
`AveragingHourPrefix.hourFailure_eq_firstFailed` and
`AveragingHourPrefix.restricted_hourFailure_measure_le` to charge the first
failed hour, `AveragingFixedSeedHours.fixed_seed_hour_failure_tail` to make the
successful earlier hours a block-start prefix event, and
`AveragingDominantLevelSplice.global_hour_failure_tail` to average the random
seed and seed-measurable selected schedule without a seed-count or level-count
factor.

No event in this file is conditioned on later receipt success or failure.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.LateStrengthening

open TimeTheorem StageEventSpec
open AveragingSparseEntry
open AveragingObservedHourTails AveragingNumerics
open AveragingDominantLevelSplice

variable {n : ℕ}

/-- The N13 selected-schedule hour-test failure family, under the original law.

In the later `hcover` for `lateSamplingSeedProducerSafeFailure`, this event is
meant to cover the branch in which the selected hour induction fails before it
can supply the `hcredit`, `hminority`, and `hpotential` hypotheses of
`lateSamplingSeedReceipt_of_checkpoint_data`; in particular it covers failure
of the retained `.9616` protected-credit test.  It does not cover the terminal
near-level tests or the old-index cutoff, which are charged by
`nearTestFailure` and `oldIndexFailure` respectively.

The definition deliberately does not intersect with the future receipt-failure
event.  The seed piece, selected schedule, and successful-earlier-hour events
used by N13 are all observed at their corresponding block starts. -/
def protectedTestFailure (init : InputCfg n) : Set (InputLog n) :=
  globalHourFailure init

/-- Membership in the protected-test family: a genuine safe Phase-3 seed in the
early horizon, followed by failure of its seed-measurable N13 schedule. -/
theorem mem_protectedTestFailure_iff
    (init : InputCfg n) (ω : InputLog n) :
    ω ∈ protectedTestFailure init ↔
      ∃ S : ℕ,
        S ≤ earlyHorizon n ∧
        SafeSparseSeed init ω S ∧
        ω ∈ scheduledHourFailure init S
          (selectedSchedule init (trace init ω S)) := by
  simp only [protectedTestFailure, globalHourFailure, Set.mem_iUnion,
    Set.mem_inter_iff, seedPiece, Set.mem_setOf_eq] <;> tauto

/-- The N13 hour budget is inside the `1 / n^4` slot reserved for
`hprotected`.  The real inequality is the sharper public theorem
`AveragingNumerics.hour_test_union_scalar`; the remaining work is only the
`ℝ`/`ℝ≥0∞` conversion and the inequality `5 * hourIndex ≤ 10 * clockHours`. -/
theorem protected_test_failure_budget {n : ℕ}
    (hn : timePopulationThreshold ≤ n) :
    5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ≥0∞) * hourError n ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 4) := by
  have hnpos : 0 < (n : ℝ) := (population_log_lower hn).1
  have hclock :
      PhaseThreeModel.Numeric.hourIndex n + 1 =
        PhaseThreeModel.Numeric.clockHours n := by
    rfl
  have hindexNat :
      PhaseThreeModel.Numeric.hourIndex n ≤
        PhaseThreeModel.Numeric.clockHours n := by
    rw [← hclock]
    omega
  have hindex :
      (PhaseThreeModel.Numeric.hourIndex n : ℝ) ≤
        (PhaseThreeModel.Numeric.clockHours n : ℝ) := by
    exact_mod_cast hindexNat
  have hclockNonneg :
      (0 : ℝ) ≤ (PhaseThreeModel.Numeric.clockHours n : ℝ) :=
    Nat.cast_nonneg _
  have hcoefficient :
      5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ) ≤
        10 * (PhaseThreeModel.Numeric.clockHours n : ℝ) := by
    calc
      5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ) ≤
          5 * (PhaseThreeModel.Numeric.clockHours n : ℝ) :=
        mul_le_mul_of_nonneg_left hindex (by norm_num)
      _ ≤ 10 * (PhaseThreeModel.Numeric.clockHours n : ℝ) := by
        nlinarith only [hclockNonneg]
  have hscalar :
      5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ) /
          (n : ℝ) ^ 20 ≤
        1 / (n : ℝ) ^ 4 := by
    calc
      5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ) /
          (n : ℝ) ^ 20 ≤
        10 * (PhaseThreeModel.Numeric.clockHours n : ℝ) /
          (n : ℝ) ^ 20 :=
        div_le_div_of_nonneg_right hcoefficient
          (pow_pos hnpos 20).le
      _ ≤ 1 / (n : ℝ) ^ 4 := hour_test_union_scalar hn
  have hcoefficientCast :
      ENNReal.ofReal
          (5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ)) =
        5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ≥0∞) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
  have hproduct :
      5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ≥0∞) * hourError n =
        ENNReal.ofReal
          (5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ) /
            (n : ℝ) ^ 20) := by
    unfold hourError
    have hdiv :
        5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ) /
            (n : ℝ) ^ 20 =
          (5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ)) *
            (1 / (n : ℝ) ^ 20) := by
      ring
    rw [hdiv, ENNReal.ofReal_mul (by positivity), hcoefficientCast]
  calc
    5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ≥0∞) * hourError n =
        ENNReal.ofReal
          (5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ) /
            (n : ℝ) ^ 20) := hproduct
    _ ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 4) :=
      ENNReal.ofReal_le_ofReal hscalar

/-- The requested `hprotected` input, under the same `GoodInput` assumptions as
the eventual N16 receipt theorem.  This is an unconditional estimate under
`law init`. -/
theorem protected_test_failure_estimate
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (protectedTestFailure init) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 4) := by
  simpa only [protectedTestFailure] using
    (global_hour_failure_tail init hinput.2.1 hinput.2.2 hinput.1).trans
      (protected_test_failure_budget hinput.1)

/-- `late_sampling_seed_receipt_safe_estimate` with the protected-test set and
its `hprotected` proof instantiated.  The other two charged families and the
set-theoretic cover remain explicit, as required by the parallel rounds. -/
theorem late_sampling_seed_receipt_safe_estimate_with_protected_tests
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (nearTestFailure oldIndexFailure : Set (InputLog n))
    (hcover :
      lateSamplingSeedProducerSafeFailure init ⊆
        protectedTestFailure init ∪ (nearTestFailure ∪ oldIndexFailure))
    (hnear :
      law init nearTestFailure ≤
        ENNReal.ofReal (1 / (n : ℝ) ^ 4))
    (hold :
      law init oldIndexFailure ≤
        ENNReal.ofReal
          (Real.rpow (n : ℝ) (-(207 / 100 : ℝ)))) :
    law init (lateSamplingSeedProducerSafeFailure init) ≤
      ENNReal.ofReal
        (2 / (n : ℝ) ^ 4 +
          Real.rpow (n : ℝ) (-(207 / 100 : ℝ))) := by
  have hprotected :
      law init (protectedTestFailure init) ≤
        ENNReal.ofReal (1 / (n : ℝ) ^ 4) :=
    protected_test_failure_estimate init hinput
  exact
    late_sampling_seed_receipt_safe_estimate init
      (protectedTestFailure init) nearTestFailure oldIndexFailure
      hcover hprotected hnear hold

end Ripple.PopulationProtocol.ExactMajority.LateStrengthening

end
