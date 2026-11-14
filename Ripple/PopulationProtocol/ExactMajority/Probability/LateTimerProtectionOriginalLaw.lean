-- Ripple/PopulationProtocol/ExactMajority/Probability/LateTimerProtectionOriginalLaw.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateTimerPrefixScalar
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingRecordedProcess
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseZeroEntry
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseOneDrainStopping
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockProducer

/-!
# Original-law protection of the late phase timers

For `5 ≤ p ≤ 8` this file holds the original-law infrastructure of the late-timer
protection: the genuine phase-`p` seed time and its fibres, the persistent-label
participation process and its conditional probability, the fixed-label
`n^(-3.06)` tail on every seed fibre, and the budgets.  The deterministic route
and the final `n^(-2.06)` statement are in `LateTimerProtectionGuarded` and
`LateTimerRouteProof`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal NNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.LateTimerProtectionOriginalLaw

open TimeTheorem PairLog PhaseOneDrain PhaseOneDrainStopping
open StageEventSpec PhaseThreeScalar
open LateTimerPrefixScalar

variable {L K n : ℕ}

/-- The genuine first time at which some agent has phase at least `p`. -/
noncomputable def phaseSeedTime
    (init : InputCfg n) (p : ℕ) : InputLog n → WithTop ℕ :=
  TraceDrain.exitTime init (someGE (n := n) p)

theorem phaseSeedTime_eq_iff
    (init : InputCfg n) (p : ℕ) (omega : InputLog n) (s : ℕ) :
    phaseSeedTime init p omega = (s : WithTop ℕ) ↔
      firstHit (someGE (n := n) p) (trace init omega) s :=
  PhaseOneDrainStopping.exitTime_eq_iff_firstHit
    init (someGE (n := n) p) omega s

theorem phaseSeedTime_past
    (init : InputCfg n) (p : ℕ) :
    PhaseOneDrain.PairLogPastTime (phaseSeedTime init p) :=
  PhaseOneDrainStopping.exitTime_pairLogPastTime
    init (someGE (n := n) p)

/-- One finite fibre of the genuine phase-`p` stopping time. -/
def phaseSeedFibre
    (init : InputCfg n) (p s : ℕ) : Set (InputLog n) :=
  {omega | phaseSeedTime init p omega = (s : WithTop ℕ)}

/-- The four timed late phases. -/
def LateTimedPhase (p : ℕ) : Prop :=
  5 ≤ p ∧ p ≤ 8

open Classical in
/-- The next-draw indicator that persistent label `i` participates, in either
orientation, at absolute step `s+t+1`. -/
noncomputable def labelParticipationFamily
    (init : Cfg L K) (i : Fin init.card) (s : ℕ) :
    AveragingRecordedProcess.IncrementFamily L K s :=
  fun t q d =>
    if ∃ j : Fin init.card, j ≠ i ∧
        (PairLog.selectLabels
            (PairLog.prefixLabels init (s + t) q) d = some (i, j) ∨
         PairLog.selectLabels
            (PairLog.prefixLabels init (s + t) q) d = some (j, i))
    then 1 else 0

/-- Participation process viewed from deterministic time `s`. -/
noncomputable def labelParticipation
    (init : Cfg L K) (i : Fin init.card) (s t : ℕ) :
    TimeTheorem.Ω L K → ℝ :=
  AveragingRecordedProcess.recordedIncrement s
    (labelParticipationFamily init i s) t

theorem labelParticipation_stronglyMeasurable
    (init : Cfg L K) (i : Fin init.card) (s t : ℕ) :
    StronglyMeasurable[
      AveragingRecordedExpectation.shiftedPairLog L K s (t + 1)]
      (labelParticipation init i s t) :=
  AveragingRecordedProcess.recordedIncrement_stronglyMeasurable
    s (labelParticipationFamily init i s) t

theorem labelParticipation_zero_or_one
    (init : Cfg L K) (i : Fin init.card) (s t : ℕ)
    (omega : TimeTheorem.Ω L K) :
    labelParticipation init i s t omega = 0 ∨
      labelParticipation init i s t omega = 1 := by
  classical
  change
    (if ∃ j : Fin init.card, j ≠ i ∧
        (PairLog.selectLabels
            (PairLog.prefixLabels init (s + t)
              (frestrictLe (s + t) omega)) (omega (s + t + 1)) =
              some (i, j) ∨
         PairLog.selectLabels
            (PairLog.prefixLabels init (s + t)
              (frestrictLe (s + t) omega)) (omega (s + t + 1)) =
              some (j, i))
      then (1 : ℝ) else 0) = 0 ∨
    (if ∃ j : Fin init.card, j ≠ i ∧
        (PairLog.selectLabels
            (PairLog.prefixLabels init (s + t)
              (frestrictLe (s + t) omega)) (omega (s + t + 1)) =
              some (i, j) ∨
         PairLog.selectLabels
            (PairLog.prefixLabels init (s + t)
              (frestrictLe (s + t) omega)) (omega (s + t + 1)) =
              some (j, i))
      then (1 : ℝ) else 0) = 1
  split_ifs <;> simp

theorem labelParticipation_conditional_probability
    (init : Cfg L K) (hc : 2 ≤ init.card)
    (i : Fin init.card) (s t : ℕ) :
    (law init)[labelParticipation init i s t |
      AveragingRecordedExpectation.shiftedPairLog L K s t]
        =ᵐ[law init] (fun _ => 2 / (init.card : ℝ)) := by
  classical
  have heq :
      labelParticipation init i s t =
        fun omega =>
          if ∃ j : Fin init.card, j ≠ i ∧
              (PairLog.drawLabels init omega (s + t + 1) = some (i, j) ∨
               PairLog.drawLabels init omega (s + t + 1) = some (j, i))
          then (1 : ℝ) else 0 := by
    funext omega
    rfl
  rw [heq]
  simpa [AveragingRecordedExpectation.shiftedPairLog] using
    (PhaseZeroEntry.selected_label_participation_conditional_probability
      init hc i (s + t))

/-- A fixed label accumulates the full counter allowance during the protection
window following time `s`. -/
def labelFastEvent
    (init : InputCfg n) (i : Fin init.card) (s : ℕ) :
    Set (InputLog n) :=
  {omega |
    ((invocationThreshold n : ℕ) : ℝ) ≤
      bernoulliCount (labelParticipation init i s)
        (protectionHorizon n) omega}

/-- The requested early-next-seed event. -/
def timerProtectionFailure
    (init : InputCfg n) (p : ℕ) : Set (InputLog n) :=
  {omega | ∃ s : ℕ,
    phaseSeedTime init p omega = (s : WithTop ℕ) ∧
      phaseSeedTime init (p + 1) omega ≤
        ((s + protectionHorizon n : ℕ) : WithTop ℕ)}

/-- Per-label `n^(-3.06)` budget. -/
noncomputable def perLabelTimerBudget (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.rpow (n : ℝ) (-(153 / 50 : ℝ)))

/-- Final timer-protection `n^(-2.06)` budget. -/
noncomputable def timerProtectionBudget (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.rpow (n : ℝ) (-(103 / 50 : ℝ)))

private theorem measure_le_of_real_le_mul
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {A E : Set Omega} {c : ℝ} (hc : 0 ≤ c)
    (h : mu.real A ≤ c * mu.real E) :
    mu A ≤ ENNReal.ofReal c * mu E := by
  have hright : ENNReal.ofReal c * mu E ≠ ∞ :=
    ENNReal.mul_ne_top (by finiteness) (measure_ne_top mu E)
  apply (ENNReal.toReal_le_toReal (measure_ne_top mu A) hright).mp
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] using h

/-- Multiplying the fixed-label budget by the population size loses exactly
one power of `n`. -/
theorem population_mul_perLabelTimerBudget
    {n : ℕ} (hn : 0 < n) :
    (n : ℝ≥0∞) * perLabelTimerBudget n =
      timerProtectionBudget n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hreal :
      (n : ℝ) * Real.rpow (n : ℝ) (-(153 / 50 : ℝ)) =
        Real.rpow (n : ℝ) (-(103 / 50 : ℝ)) := by
    calc
      (n : ℝ) * Real.rpow (n : ℝ) (-(153 / 50 : ℝ)) =
          Real.exp (Real.log (n : ℝ)) *
            Real.exp (Real.log (n : ℝ) * (-(153 / 50 : ℝ))) := by
        rw [Real.exp_log hnR]
        exact congrArg (fun x => (n : ℝ) * x)
          (Real.rpow_def_of_pos hnR (-(153 / 50 : ℝ)))
      _ = Real.exp
          (Real.log (n : ℝ) +
            Real.log (n : ℝ) * (-(153 / 50 : ℝ))) := by
        rw [← Real.exp_add]
      _ = Real.exp
          (Real.log (n : ℝ) * (-(103 / 50 : ℝ))) := by
        congr 1
        ring
      _ = Real.rpow (n : ℝ) (-(103 / 50 : ℝ)) :=
        (Real.rpow_def_of_pos hnR (-(103 / 50 : ℝ))).symm
  unfold perLabelTimerBudget timerProtectionBudget
  rw [show (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) by
        rw [ENNReal.ofReal_natCast],
      ← ENNReal.ofReal_mul (Nat.cast_nonneg n), hreal]

/-- A stopping-time fibre is measurable at time zero of the shifted
filtration. -/
theorem phaseSeedFibre_measurable
    (init : InputCfg n) (p s : ℕ) :
    MeasurableSet[
      AveragingRecordedExpectation.shiftedPairLog
        (PhaseThreeModel.Numeric.hourIndex n) 256 s 0]
      (phaseSeedFibre init p s) := by
  simpa [phaseSeedFibre,
    AveragingRecordedExpectation.shiftedPairLog] using
      ((phaseSeedTime_past init p) s)

/-- Fixed-label protection tail on one genuine phase-`p` seed fibre. -/
theorem labelFastEvent_seedFibre_tail
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (p s : ℕ) (i : Fin init.card) :
    law init (phaseSeedFibre init p s ∩ labelFastEvent init i s) ≤
      perLabelTimerBudget n * law init (phaseSeedFibre init p s) := by
  have hnforty : 40 ≤ n :=
    (TimeTheorem.time_population_bounds hinput.1).2
  have hc : 2 ≤ init.card := by
    rw [hinput.2.2]
    omega
  have hstrong : ∀ t,
      StronglyMeasurable[
        AveragingRecordedExpectation.shiftedPairLog
          (PhaseThreeModel.Numeric.hourIndex n) 256 s (t + 1)]
        (labelParticipation init i s t) :=
    fun t => labelParticipation_stronglyMeasurable init i s t
  have hzeroOne : ∀ t, ∀ᵐ omega ∂law init,
      labelParticipation init i s t omega = 0 ∨
        labelParticipation init i s t omega = 1 :=
    fun t => ae_of_all _ fun omega =>
      labelParticipation_zero_or_one init i s t omega
  have hprob : ∀ t,
      (law init)[labelParticipation init i s t |
        AveragingRecordedExpectation.shiftedPairLog
          (PhaseThreeModel.Numeric.hourIndex n) 256 s t]
        =ᵐ[law init] (fun _ => 2 / (n : ℝ)) := by
    intro t
    simpa [hinput.2.2] using
      (labelParticipation_conditional_probability init hc i s t)
  have hreal :=
    LateTimerPrefixScalar.late_timer_lower_prefix_scalar
      (mu := law init)
      (filtration := AveragingRecordedExpectation.shiftedPairLog
        (PhaseThreeModel.Numeric.hourIndex n) 256 s)
      hinput.1
      (labelParticipation init i s)
      hstrong hzeroOne hprob
      (phaseSeedFibre init p s)
      (phaseSeedFibre_measurable init p s)
  have hmeasure := measure_le_of_real_le_mul
    (law init) (Real.rpow_nonneg (Nat.cast_nonneg n) _) hreal
  simpa [perLabelTimerBudget, labelFastEvent] using hmeasure

/-!
THEOREM LIST
* `phaseSeedTime`
* `phaseSeedTime_eq_iff`
* `phaseSeedTime_past`
* `LateTimedPhase`
* `labelParticipation`
* `labelParticipation_stronglyMeasurable`
* `labelParticipation_conditional_probability`
* `labelFastEvent`
* `timerProtectionFailure`
* `population_mul_perLabelTimerBudget`
* `labelFastEvent_seedFibre_tail`

CLOSES
* The exact adapted Bernoulli participation process for every persistent label.
* The per-label `n^(-3.06)` tail on every genuine first-seed fibre.
* No conditioning on any future success event.

UNFINISHED
* Nothing in this file; the deterministic route and the `n^(-2.06)` union are in
  `LateTimerProtectionGuarded` and `LateTimerRouteProof`.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateTimerProtectionOriginalLaw

end
