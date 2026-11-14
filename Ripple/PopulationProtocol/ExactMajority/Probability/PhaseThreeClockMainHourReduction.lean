-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockMainHourReduction.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMainAssembly

/-!
# Hour-by-hour reduction of the guarded Main row

A failure of `RowMain` selects one of `clockHours n = hourIndex n + 1`
hours and one of the two inequalities.  This file performs exactly that
selection and the `n⁻³⁰` to `n⁻²⁹` union.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainHourReduction

open TimeTheorem StageEventSpec PhaseThreeClockProducer PhaseThreeClockCore PhaseThreeClockVirtual
  PhaseThreeClockRows PhaseThreeClockRowsGuarded PhaseThreeClockMainAssembly
open PhaseThreeModel.Numeric

variable {n : ℕ} (init : InputCfg n)

/-- A failure of one of the two Main inequalities at a fixed hour. -/
def MainHourViolation (h S : ℕ) (ω : InputLog n) : Prop :=
  (∃ v, S ≤ v ∧ v ≤ (virtualTimes init ω S).finish h ∧
    3 * timeMainCount (virtualCfg init ω S) <
      2500 * highHourMainsL init (virtualLabels init ω S)
        (virtualLabels init ω v) h) ∨
  (∃ v, S ≤ v ∧ v ≤ (virtualTimes init ω S).finish h ∧
    3 * timeMainCount (virtualCfg init ω S) <
      1250 * (highHourZeroMainsL init (virtualLabels init ω S)
        (virtualLabels init ω v) h +
        deepBiasedMainsL init (virtualLabels init ω S)
          (virtualLabels init ω v) h))

/-- The guarded failure event for one selected hour. -/
def guardedMainHourFailure (h : ℕ) : Set (InputLog n) :=
  {ω | ∃ S T : ℕ,
    seedTime init 3 ω = (S : WithTop ℕ) ∧
    T ≤ earlyHorizon n ∧
    AsyncEntry init ω S T ∧
    guardMain init ω S T ∧
    h ≤ hourIndex n ∧
    MainHourViolation init h S ω}

/-- Every guarded Main-row failure belongs to one of the `clockHours n`
fixed-hour failure events. -/
theorem guarded_main_failure_subset_hour_union :
    guardedFailure init (guardMain init) (mainRow init) ⊆
      ⋃ h : Fin (clockHours n), guardedMainHourFailure init h.val := by
  classical
  rintro ω ⟨S, T, hseed, hT, hentry, hguard, hbad⟩
  by_contra hnot
  apply hbad
  change RowMain init (virtualLabels init ω) (virtualCfg init ω) S
    (virtualTimes init ω S)
  refine ⟨?_, ?_⟩
  · intro h hh v hSv hv
    by_contra hineq
    have hfin : h < clockHours n := by
      unfold clockHours
      omega
    have hstrict :
        3 * timeMainCount (virtualCfg init ω S) <
          2500 * highHourMainsL init (virtualLabels init ω S)
            (virtualLabels init ω v) h := by
      omega
    apply hnot
    refine Set.mem_iUnion.mpr ⟨⟨h, hfin⟩, ?_⟩
    exact ⟨S, T, hseed, hT, hentry, hguard, hh,
      Or.inl ⟨v, hSv, hv, hstrict⟩⟩
  · intro h hh v hSv hv
    by_contra hineq
    have hfin : h < clockHours n := by
      unfold clockHours
      omega
    have hstrict :
        3 * timeMainCount (virtualCfg init ω S) <
          1250 * (highHourZeroMainsL init (virtualLabels init ω S)
            (virtualLabels init ω v) h +
            deepBiasedMainsL init (virtualLabels init ω S)
              (virtualLabels init ω v) h) := by
      omega
    apply hnot
    refine Set.mem_iUnion.mpr ⟨⟨h, hfin⟩, ?_⟩
    exact ⟨S, T, hseed, hT, hentry, hguard, hh,
      Or.inr ⟨v, hSv, hv, hstrict⟩⟩

/-- The exact finite-hour coefficient used by the guarded Main row. -/
theorem main_hour_union_coefficient
    (hn : timePopulationThreshold ≤ n) :
    (clockHours n : ℝ≥0∞) * ENNReal.ofReal (1 / (n : ℝ) ^ 30) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 29) := by
  have hlow : (6 / 25 : ℝ) * (n : ℝ) ≤ (n : ℝ) := by
    have hnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  obtain ⟨hnp, -, -, -, -, -, -, -, -, -, -, -, hhours, -⟩ :=
    numeric_calibration_core (time_population_bounds hn).1 hlow le_rfl
  have hcast : (clockHours n : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
    exact_mod_cast hhours
  calc
    _ ≤ (n : ℝ≥0∞) * ENNReal.ofReal (1 / (n : ℝ) ^ 30) :=
      mul_le_mul_right' hcast _
    _ = ENNReal.ofReal ((n : ℝ) * (1 / (n : ℝ) ^ 30)) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
    _ = _ := by
      congr 1
      rw [show (30 : ℕ) = 29 + 1 from rfl, pow_succ]
      field_simp [ne_of_gt hnp]

/-- A uniform `n⁻³⁰` bound for the fixed-hour guarded events gives the exact
`GuardedRowTails.main` field. -/
theorem guarded_main_tail_of_hour_tails
    (hn : timePopulationThreshold ≤ n)
    (hhour : ∀ h : Fin (clockHours n),
      law init (guardedMainHourFailure init h.val) ≤
        ENNReal.ofReal (1 / (n : ℝ) ^ 30)) :
    law init (guardedFailure init (guardMain init) (mainRow init)) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 29) := by
  calc
    _ ≤ law init (⋃ h : Fin (clockHours n),
        guardedMainHourFailure init h.val) :=
      measure_mono (guarded_main_failure_subset_hour_union init)
    _ ≤ ∑' h : Fin (clockHours n),
        law init (guardedMainHourFailure init h.val) :=
      measure_iUnion_le _
    _ ≤ ∑' _h : Fin (clockHours n),
        ENNReal.ofReal (1 / (n : ℝ) ^ 30) :=
      ENNReal.tsum_le_tsum hhour
    _ = (clockHours n : ℝ≥0∞) *
        ENNReal.ofReal (1 / (n : ℝ) ^ 30) := by
      simp [tsum_fintype, nsmul_eq_mul]
    _ ≤ _ := main_hour_union_coefficient hn

/-- Once the fixed-hour estimates and the already separated step-3 rows are
available, this is the requested N12 headline. -/
theorem asynchronous_clock_estimate_of_hour_tails
    (hinput : ThresholdEpidemic.GoodInput n init)
    (hthree : StepThreeRows init)
    (hhour : ∀ h : Fin (clockHours n),
      law init (guardedMainHourFailure init h.val) ≤
        ENNReal.ofReal (1 / (n : ℝ) ^ 30)) :
    law init (phaseClockFailure (reviewedStageEvents n init)) ≤
      ENNReal.ofReal (8 / (n : ℝ) ^ 5) :=
  asynchronous_clock_estimate_of_four_rows init hinput hthree
    (guarded_main_tail_of_hour_tails init hinput.1 hhour)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainHourReduction

end
