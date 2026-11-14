-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingWorkBudget.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingTerminalDebtDeadlines
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingOldBlocks
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingCancellationProbability

/-!
# Old-potential work fits the compiled raw-hour budget

The compiled rawWork and clockHistory_raw_work_fits already account for the
warmup, potential and cancellation ceilings. The old fixed-potential block
has one 100 n^2/M ceiling, which is no larger than their 60-plus-40 ceilings.
No additional physical block is charged for the minority cancellation test.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.AveragingWorkBudget

open TimeTheorem StageEventSpec AveragingNumerics
open AveragingTerminalDebtDeadlines AveragingOldBlocks
open AveragingCancellationAlgebra AveragingCancellationProbability

theorem oldWorkTrials_le_potential_add_cancellation (n M : ℕ) :
    oldWorkTrials n M ≤ potentialTrials n M + cancellationTrials n M := by
  unfold oldWorkTrials
  apply Nat.ceil_le.mpr
  have hp : (60 : ℝ) * (n : ℝ) ^ 2 / M ≤ (potentialTrials n M : ℝ) :=
    Nat.le_ceil _
  have hc : (40 : ℝ) * (n : ℝ) ^ 2 / M ≤ (cancellationTrials n M : ℝ) :=
    Nat.le_ceil _
  have hsum :
      (100 : ℝ) * (n : ℝ) ^ 2 / M ≤
        (potentialTrials n M : ℝ) + (cancellationTrials n M : ℝ) := by
    calc
      (100 : ℝ) * (n : ℝ) ^ 2 / M =
          (60 : ℝ) * (n : ℝ) ^ 2 / M +
            (40 : ℝ) * (n : ℝ) ^ 2 / M := by ring
      _ ≤ _ := add_le_add hp hc
  simpa only [Nat.cast_add] using hsum

theorem oldWork_le_rawWork (n C M : ℕ) :
    clockWarmup n C + oldWorkTrials n M ≤ rawWork n M C := by
  have h := oldWorkTrials_le_potential_add_cancellation n M
  change clockWarmup n C + oldWorkTrials n M ≤
    clockWarmup n C + potentialTrials n M + cancellationTrials n M
  omega

theorem clockHistory_oldWork_before_finish {n : ℕ}
    {init : InputCfg n} {ω : InputLog n} {S T ρ : ℕ}
    {w : ClockTimes init} (h : ClockHistory init ω S T ρ w) (hn : 0 < n)
    (k : ℕ) (hk : k ≤ PhaseThreeModel.Numeric.hourIndex n) :
    w.start k + clockWarmup n (clockCount (trace init ω S)) +
        oldWorkTrials n (timeMainCount (trace init ω S)) < w.finish k := by
  have hfit := clockHistory_raw_work_fits h hn k hk
  have hbudget := oldWork_le_rawWork n
    (clockCount (trace init ω S)) (timeMainCount (trace init ω S))
  have hle :
      w.start k + (clockWarmup n (clockCount (trace init ω S)) +
          oldWorkTrials n (timeMainCount (trace init ω S))) ≤
        w.start k +
          rawWork n (timeMainCount (trace init ω S)) (clockCount (trace init ω S)) :=
    add_le_add le_rfl hbudget
  simpa only [Nat.add_assoc] using hle.trans_lt hfit

theorem clockHistory_oldWork_before_next {n : ℕ}
    {init : InputCfg n} {ω : InputLog n} {S T ρ : ℕ}
    {w : ClockTimes init} (h : ClockHistory init ω S T ρ w) (hn : 0 < n)
    (k : ℕ) (hk : k + 1 ≤ PhaseThreeModel.Numeric.hourIndex n) :
    w.start k + clockWarmup n (clockCount (trace init ω S)) +
        oldWorkTrials n (timeMainCount (trace init ω S)) < w.start (k + 1) := by
  have hfit := clockHistory_oldWork_before_finish h hn k (by omega)
  have hnext := h.previous_end (k + 1) (by omega) hk
  have hpred : k + 1 - 1 = k := by omega
  rw [hpred] at hnext
  exact hfit.trans hnext

end Ripple.PopulationProtocol.ExactMajority.AveragingWorkBudget

end
