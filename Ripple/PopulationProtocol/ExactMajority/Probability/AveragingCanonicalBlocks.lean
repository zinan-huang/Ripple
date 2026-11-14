-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingCanonicalBlocks.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingClockBlocks
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingSeededDelay
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingRandomOldBlocks

/-!
# Canonical clock blocks in the observed old-index extinction estimate

All block starts, the earlier potential checkpoint, and the current warmup
endpoint are actual pair-log past-time functions. The warmup length is read
from the recorded seed configuration, so its random clock count is retained.

The probability statement still intersects the actual WorkLive event. Proving
that prior successful hours supply that event, and the earlier potential cap,
is the remaining global hour-induction obligation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.AveragingCanonicalBlocks

open TimeTheorem PairLog PhaseOneDrain StageEventSpec PhaseThreeClockProducer
open AveragingNumerics AveragingOldBlocks AveragingWorkCounter AveragingObservedBlocks
open AveragingClockBlocks AveragingSeededDelay AveragingRandomOldBlocks
open AveragingTerminalDebtDeadlines

variable {n : ℕ}

def oldBlockStarts (init : InputCfg n) (seed : InputLog n → WithTop ℕ)
    (r q : ℕ) (j : Fin (q - 6)) : InputLog n → WithTop ℕ :=
  hourWarmStart init seed (r + 1 + j.val)

theorem oldBlockStarts_pastTime (init : InputCfg n)
    (seed : InputLog n → WithTop ℕ) (hseed : PairLogPastTime seed)
    (r q : ℕ) (j : Fin (q - 6)) :
    PairLogPastTime (oldBlockStarts init seed r q j) :=
  hourWarmStart_pastTime init seed hseed (r + 1 + j.val)

theorem oldCutoff_ge_seven (hn : timePopulationThreshold ≤ n) :
    7 ≤ oldCutoff n := by
  have hlog := (population_log_lower hn).2
  have hfloor := Nat.lt_floor_add_one (Real.log (n : ℝ) / 3)
  have hr : (7 : ℝ) ≤ (oldCutoff n : ℝ) := by
    dsimp [oldCutoff]
    linarith only [hfloor, hlog]
  exact_mod_cast hr

theorem oldBlockStarts_clockHistory {init : InputCfg n} {ω : InputLog n}
    {S T ρ : ℕ} {w : ClockTimes init} (H : ClockHistory init ω S T ρ w)
    (seed : InputLog n → WithTop ℕ) (hseed : seed ω = (S : WithTop ℕ))
    (r q : ℕ) (hrq : r + q ≤ PhaseThreeModel.Numeric.hourIndex n)
    (j : Fin (q - 6)) :
    oldBlockStarts init seed r q j ω =
      ((w.start (r + 1 + j.val) +
        clockWarmup n (clockCount (trace init ω S)) : ℕ) : WithTop ℕ) :=
  hourWarmStart_clockHistory H seed (r + 1 + j.val) hseed
    (by have hj := j.isLt; omega)

/-- Completion and ordering for the canonical random-seed clock blocks. -/
theorem canonical_old_blocks_complete {init : InputCfg n} {ω : InputLog n}
    {S T ρ : ℕ} {w : ClockTimes init} (H : ClockHistory init ω S T ρ w)
    (hn : 0 < n) (seed : InputLog n → WithTop ℕ)
    (hseed : seed ω = (S : WithTop ℕ)) (r q : ℕ) (hq : 7 ≤ q)
    (hrq : r + q ≤ PhaseThreeModel.Numeric.hourIndex n) :
    let C := clockCount (trace init ω S)
    let M := timeMainCount (trace init ω S)
    let P := w.start r + clockWarmup n C + potentialTrials n M
    let W := w.start (r + q) + clockWarmup n C
    BlocksComplete P (oldWorkTrials n M) (oldBlockStarts init seed r q) (W - P) ω :=
  clockHistory_old_blocks_complete H hn r q hq hrq
    (oldBlockStarts init seed r q)
    (fun j => oldBlockStarts_clockHistory H seed hseed r q hrq j)

/-- This event uses canonical random clock times throughout. M and the
integer cap Ψ are fixed local parameters; the WorkLive gate contains their
required actual configuration bounds. -/
theorem canonical_old_blocks_tail (init : InputCfg n)
    (seed : InputLog n → WithTop ℕ) (hseed : PairLogPastTime seed)
    (r : ℕ) (hr : 1 ≤ r) (M Ψ : ℕ)
    (hn : timePopulationThreshold ≤ n) (hMpos : 0 < M) (hMle : M ≤ n)
    (hΨ : (Ψ : ℝ) ≤ (1 / 1000 : ℝ) * n) :
    law init (randomBlocksFailure init
        (hourPotentialEnd init seed r)
        (hourWarmStart init seed (r + oldCutoff n)) r
        (ENNReal.ofReal (oldWorkRate n M)) Ψ (oldWorkTrials n M)
        (oldBlockStarts init seed r (oldCutoff n))) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 20) :=
  old_blocks_tail_between_pastTimes n M hn hMpos hMle init
    (hourPotentialEnd init seed r) (hourWarmStart init seed (r + oldCutoff n))
    (hourPotentialEnd_pastTime init seed hseed r)
    (hourWarmStart_pastTime init seed hseed (r + oldCutoff n))
    r hr Ψ hΨ (oldBlockStarts init seed r (oldCutoff n))
    (fun j => oldBlockStarts_pastTime init seed hseed r (oldCutoff n) j)

theorem canonical_old_blocks_phaseThreeSeed_tail (init : InputCfg n)
    (r : ℕ) (hr : 1 ≤ r) (M Ψ : ℕ)
    (hn : timePopulationThreshold ≤ n) (hMpos : 0 < M) (hMle : M ≤ n)
    (hΨ : (Ψ : ℝ) ≤ (1 / 1000 : ℝ) * n) :
    law init (randomBlocksFailure init
        (hourPotentialEnd init (seedTime init 3) r)
        (hourWarmStart init (seedTime init 3) (r + oldCutoff n)) r
        (ENNReal.ofReal (oldWorkRate n M)) Ψ (oldWorkTrials n M)
        (oldBlockStarts init (seedTime init 3) r (oldCutoff n))) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 20) :=
  canonical_old_blocks_tail init (seedTime init 3) (seedTime_pastTime init 3)
    r hr M Ψ hn hMpos hMle hΨ

end Ripple.PopulationProtocol.ExactMajority.AveragingCanonicalBlocks

end
