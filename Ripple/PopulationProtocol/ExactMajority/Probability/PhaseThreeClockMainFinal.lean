-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockMainFinal.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMainBarrier
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMainExponent
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockGuardedInitialTails

/-!
# Final guarded Main row and the N12 clock headline
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainFinal

open TimeTheorem PairLog StageEventSpec PhaseThreeClockProducer
  PhaseThreeClockRows PhaseThreeClockRowsGuarded
  PhaseThreeClockMainAssembly PhaseThreeClockMainTerminal
  PhaseThreeClockMainHourReduction PhaseThreeClockMainProcess
  PhaseThreeClockMainProcessIncrement PhaseThreeClockMainProcessDrift
  PhaseThreeClockMainBarrier PhaseThreeClockGuardedInitialTails
  PhaseThreeClockBulkShapeBudget
open PhaseThreeModel.Numeric

variable {n : ℕ} (init : InputCfg n)

noncomputable def main_hour_terminal_certificate
    (hn : populationThreshold ≤ n) (hcard : init.card = n)
    (h : Fin (clockHours n)) :
    HourTerminalCertificate init (guardedMainHourFailure init h.val) := by
  have hex := main_exponent_calibration hn
  have hspec := Classical.choose_spec hex
  have hh : h.val ≤ hourIndex n := by
    have hh := h.isLt
    unfold clockHours at hh
    omega
  have hnTwo : 2 ≤ n := by
    have hlarge := (strong_bulk_family_calibration hn).1
    omega
  have hcardTwo : 2 ≤ init.card := by
    rw [hcard]
    exact hnTwo
  exact
    { Y := mainProcessY init h.val
      lam := Classical.choose hex
      adapted := mainProcessY_adapted init h.val
      increment := mainProcessY_increment init h.val
      drift := mainProcessY_drift init h.val hh hcardTwo
      barrier := guardedMainHourFailure_subset_barrier init hn h
      lam_nonneg := hspec.1
      lam_jump := hspec.2.1
      exponent := hspec.2.2 }

noncomputable def main_hour_terminal_certificates
    (hn : populationThreshold ≤ n) (hcard : init.card = n) :
    ∀ h : Fin (clockHours n),
      HourTerminalCertificate init (guardedMainHourFailure init h.val) :=
  fun h => main_hour_terminal_certificate init hn hcard h

/-- The unconditional guarded Main field with its exact `n⁻²⁹` budget. -/
theorem guarded_main_row_tail
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (guardedFailure init (guardMain init) (mainRow init)) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 29) := by
  have hn : populationThreshold ≤ n := (time_population_bounds hinput.1).1
  exact guarded_main_tail_of_terminal_certificates init hinput.1
    (main_hour_terminal_certificates init hn hinput.2.2)

/-- The complete guarded §11 row package, now with the Main field filled. -/
theorem guarded_main_row_tails
    (hinput : ThresholdEpidemic.GoodInput n init) :
    GuardedRowTails init :=
  guarded_row_tails_of_main init hinput (guarded_main_row_tail init hinput)

/-- The N12 theorem in the exact type of `DOTY-LEAN-PLAN`. -/
theorem asynchronous_clock_estimate
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (phaseClockFailure (reviewedStageEvents n init)) ≤
      ENNReal.ofReal (8 / (n : ℝ) ^ 5) := by
  have hn : populationThreshold ≤ n := (time_population_bounds hinput.1).1
  have hstep := step_three_row_tails init hn
  let hthree : StepThreeRows init :=
    { activation := hstep.activation
      passage := hstep.passage
      shape := hstep.shape }
  exact asynchronous_clock_estimate_of_terminal_certificates init hinput hthree
    (main_hour_terminal_certificates init hn hinput.2.2)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainFinal

end
