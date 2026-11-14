-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockMainTerminal.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMainExponential
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMainHourReduction

/-!
# Terminal reduction for the guarded Main row

The concrete process is deliberately abstracted as a certificate.  This file
contains the exact application of `supermartingale_terminal_tail`, the fixed-hour
bound, the finite-hour union, and the N12 assembly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainTerminal

open TimeTheorem PairLog PhaseThreeClockMainExponential
  PhaseThreeClockMainHourReduction PhaseThreeClockMainAssembly
open PhaseThreeModel.Numeric
open Ripple.Probability StageEventSpec PhaseThreeClockRowsGuarded PhaseThreeClockRows

variable {n : ℕ} (init : InputCfg n)

/-- A deterministic horizon containing every guarded seed, cap, and local Main
window. -/
def mainTerminalHorizon (n : ℕ) : ℕ :=
  earlyHorizon n + logWindow n 20000 + logWindow n 30

/-- The bounded-increment constant charged by the Main process. -/
def mainJumpBound (n : ℕ) : ℝ := 10 / (n : ℝ)

/-- The discounted barrier used for the fixed-hour terminal event. -/
def mainBarrierRise (n : ℕ) : ℝ :=
  (9 / 100000 : ℝ) * Real.rpow (n : ℝ) (-2 / 25 : ℝ)

theorem mainJumpBound_nonneg (n : ℕ) : 0 ≤ mainJumpBound n := by
  unfold mainJumpBound
  exact div_nonneg (by norm_num) (Nat.cast_nonneg n)

/-- Everything the concrete killed process must provide for one measurable bad
event.  The last field is the separate scalar calibration obligation. -/
structure HourTerminalCertificate (B : Set (InputLog n)) where
  Y : ℕ → InputLog n → ℝ
  lam : ℝ
  adapted : ∀ t,
    StronglyMeasurable[
      pairLogFiltration (hourIndex n) 256 t] (Y t)
  increment : ∀ t ω,
    |Y (t + 1) ω - Y t ω| ≤ mainJumpBound n
  drift : ∀ t,
    (law init)[fun ω => Y (t + 1) ω - Y t ω |
        pairLogFiltration (hourIndex n) 256 t] ≤ᵐ[law init]
      fun _ => 0
  barrier : B ⊆
    {ω | mainBarrierRise n ≤
      Y (mainTerminalHorizon n) ω - Y 0 ω}
  lam_nonneg : 0 ≤ lam
  lam_jump : lam * mainJumpBound n < 3
  exponent :
    ENNReal.ofReal (Real.exp (
      (mainTerminalHorizon n : ℝ) *
          (bernstein_psi lam (mainJumpBound n) * mainJumpBound n ^ 2) -
        lam * mainBarrierRise n)) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 30)

/-- The terminal Bennett/Bernstein estimate on one certified bad event. -/
theorem terminal_tail_of_certificate
    {B : Set (InputLog n)}
    (cert : HourTerminalCertificate init B) :
    law init B ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 30) := by
  have htail := supermartingale_terminal_tail
    (μ := law init)
    (ℱ := pairLogFiltration (hourIndex n) 256)
    (Y := cert.Y)
    (c := mainJumpBound n)
    (mainJumpBound_nonneg n)
    cert.adapted cert.increment cert.drift
    Set.univ MeasurableSet.univ
    (mainTerminalHorizon n) (mainBarrierRise n)
    (lam := cert.lam) cert.lam_nonneg cert.lam_jump
  calc
    law init B ≤ law init
        {ω | mainBarrierRise n ≤
          cert.Y (mainTerminalHorizon n) ω - cert.Y 0 ω} :=
      measure_mono cert.barrier
    _ = law init (Set.univ ∩
        {ω | mainBarrierRise n ≤
          cert.Y (mainTerminalHorizon n) ω - cert.Y 0 ω}) := by
      simp only [Set.univ_inter]
    _ ≤ ENNReal.ofReal (Real.exp (
        (mainTerminalHorizon n : ℝ) *
            (bernstein_psi cert.lam (mainJumpBound n) *
              mainJumpBound n ^ 2) -
          cert.lam * mainBarrierRise n)) * law init Set.univ := htail
    _ = ENNReal.ofReal (Real.exp (
        (mainTerminalHorizon n : ℝ) *
            (bernstein_psi cert.lam (mainJumpBound n) *
              mainJumpBound n ^ 2) -
          cert.lam * mainBarrierRise n)) := by
      simp
    _ ≤ _ := cert.exponent

/-- A certificate for every hour fills the exact guarded Main field. -/
theorem guarded_main_tail_of_terminal_certificates
    (hn : timePopulationThreshold ≤ n)
    (cert : ∀ h : Fin (clockHours n),
      HourTerminalCertificate init
        (guardedMainHourFailure init h.val)) :
    law init (guardedFailure init (guardMain init) (mainRow init)) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 29) :=
  guarded_main_tail_of_hour_tails init hn fun h =>
    terminal_tail_of_certificate init (cert h)

/-- The requested N12 headline, conditional only on the concrete hourly process
certificates and the separately supplied step-3 rows. -/
theorem asynchronous_clock_estimate_of_terminal_certificates
    (hinput : ThresholdEpidemic.GoodInput n init)
    (hthree : StepThreeRows init)
    (cert : ∀ h : Fin (clockHours n),
      HourTerminalCertificate init
        (guardedMainHourFailure init h.val)) :
    law init (phaseClockFailure (reviewedStageEvents n init)) ≤
      ENNReal.ofReal (8 / (n : ℝ) ^ 5) :=
  asynchronous_clock_estimate_of_four_rows init hinput hthree
    (guarded_main_tail_of_terminal_certificates init hinput.1 cert)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainTerminal

end
