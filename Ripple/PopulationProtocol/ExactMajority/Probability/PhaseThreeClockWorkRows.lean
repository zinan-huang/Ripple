-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockWorkRows.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockHourWork
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockHourOccupancyRow

/-!
# Work rows use the raw-width failure budget

SeedProfile supplies all numerical premises of HourWork. Therefore either
work-field failure on the genuine seed/entry/hour-passage event is already
a raw_width failure. There is no independent work error to charge.

The estimates here compare actual row events. The missing quantitative
raw-width producer is not replaced by an assumption that a work tail holds.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockWorkRows

open TimeTheorem PairLog StageEventSpec PhaseThreeClockProducer
  PhaseThreeClockVirtual PhaseThreeClockCore PhaseThreeClockSeedTails
  PhaseThreeClockRawLocalRow PhaseThreeClockActivationRows
  PhaseThreeClockHourWork PhaseThreeClockHourOccupancyRow

variable {n : ℕ}

theorem role_counts_le_card (c : InputCfg n) :
    timeMainCount c + clockCount c + reserveCount c ≤ c.card := by
  classical
  induction c using Multiset.induction_on with
  | empty => simp [timeMainCount, clockCount, reserveCount]
  | @cons a c ih =>
      cases hr : a.role <;>
        simp_all [timeMainCount, clockCount, reserveCount, hr] <;> omega

theorem seed_work_geometry (init : InputCfg n) (hn : 1 ≤ n)
    (ω : InputLog n) (s : ℕ) (hseed : ω ∈ seedPrefix init s) :
    1 ≤ clockCount (virtualCfg init ω s) ∧
      clockCount (virtualCfg init ω s) ≤ n ∧
      12 * n ≤ 25 * timeMainCount (virtualCfg init ω s) ∧
      25 * clockCount (virtualCfg init ω s) ≤ 7 * n := by
  obtain ⟨hM, hC⟩ := seed_role_density init ω s hseed
  have hR : 6 * n ≤ 25 * reserveCount (virtualCfg init ω s) := by
    rw [virtualCfg_eq_trace_at_seedPrefix init ω s hseed]
    have hr := hseed.2.role_good.2.2.2.2
    change (1 - (1 / 25 : ℝ)) * (n : ℝ) / 4 ≤
      (reserveCount (trace init ω s) : ℝ) at hr
    have hreal : (6 : ℝ) * (n : ℝ) ≤
        25 * (reserveCount (trace init ω s) : ℝ) := by linarith
    exact_mod_cast hreal
  have hcard : (virtualCfg init ω s).card = n := by
    rw [virtualCfg_eq_trace_at_seedPrefix init ω s hseed]
    exact hseed.2.card_eq
  have hsum := role_counts_le_card (virtualCfg init ω s)
  rw [hcard] at hsum
  omega

def RawWidthRow (init : InputCfg n) (ω : InputLog n) (s : ℕ)
    (w : ClockTimes init) : Prop :=
  ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    70 * n ^ 2 < clockCount (virtualCfg init ω s) * (w.finish h - w.start h)

def FirstWorkRow (init : InputCfg n) (ω : InputLog n) (s : ℕ)
    (w : ClockTimes init) : Prop :=
  ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    Nat.ceil ((2 : ℝ) * (n : ℝ) ^ 2 / (clockCount (virtualCfg init ω s) : ℝ)) +
      Nat.ceil ((47 : ℝ) * (n : ℝ) ^ 2 / (timeMainCount (virtualCfg init ω s) : ℝ)) + 1 ≤
        w.finish h - w.start h

def SecondWorkRow (init : InputCfg n) (ω : InputLog n) (s : ℕ)
    (w : ClockTimes init) : Prop :=
  ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    Nat.ceil ((51 : ℝ) * (n : ℝ) ^ 2 / (timeMainCount (virtualCfg init ω s) : ℝ)) ≤
      w.finish h - w.start h

theorem work_rows_of_rawWidth (init : InputCfg n) (hn : 1 ≤ n)
    (ω : InputLog n) (s : ℕ) (w : ClockTimes init)
    (hseed : ω ∈ seedPrefix init s) (hwidth : RawWidthRow init ω s w) :
    FirstWorkRow init ω s w ∧ SecondWorkRow init ω s w := by
  obtain ⟨hC, hCn, hM, hCup⟩ := seed_work_geometry init hn ω s hseed
  exact core_work_allowances_of_raw_width init (virtualCfg init ω) s w hn
    hC hCn ⟨hM, hCup⟩ hwidth

def workFailureAt (init : InputCfg n) (s : ℕ)
    (row : InputLog n → ClockTimes init → Prop) : Set (InputLog n) :=
  {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
    SeedProfile n init (trace init ω s) ∧
    ∃ T, ∃ w : ClockTimes init, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T ∧
      HourPassages init ω s w ∧ ¬ row ω w}

theorem firstWorkFailure_subset_rawWidthFailure (init : InputCfg n) (hn : 1 ≤ n)
    (s : ℕ) :
    workFailureAt init s (fun ω w => FirstWorkRow init ω s w) ⊆
      workFailureAt init s (fun ω w => RawWidthRow init ω s w) := by
  rintro ω ⟨hs, hsp, T, w, hT, hentry, hpass, hbad⟩
  refine ⟨hs, hsp, T, w, hT, hentry, hpass, ?_⟩
  intro hwidth
  exact hbad (work_rows_of_rawWidth init hn ω s w ⟨hs, hsp⟩ hwidth).1

theorem secondWorkFailure_subset_rawWidthFailure (init : InputCfg n) (hn : 1 ≤ n)
    (s : ℕ) :
    workFailureAt init s (fun ω w => SecondWorkRow init ω s w) ⊆
      workFailureAt init s (fun ω w => RawWidthRow init ω s w) := by
  rintro ω ⟨hs, hsp, T, w, hT, hentry, hpass, hbad⟩
  refine ⟨hs, hsp, T, w, hT, hentry, hpass, ?_⟩
  intro hwidth
  exact hbad (work_rows_of_rawWidth init hn ω s w ⟨hs, hsp⟩ hwidth).2

theorem seed_first_work_failure_le_raw_width (init : InputCfg n) (hn : 1 ≤ n)
    (s : ℕ) :
    law init (workFailureAt init s (fun ω w => FirstWorkRow init ω s w)) ≤
      law init (workFailureAt init s (fun ω w => RawWidthRow init ω s w)) :=
  measure_mono (firstWorkFailure_subset_rawWidthFailure init hn s)

theorem seed_second_work_failure_le_raw_width (init : InputCfg n) (hn : 1 ≤ n)
    (s : ℕ) :
    law init (workFailureAt init s (fun ω w => SecondWorkRow init ω s w)) ≤
      law init (workFailureAt init s (fun ω w => RawWidthRow init ω s w)) :=
  measure_mono (secondWorkFailure_subset_rawWidthFailure init hn s)

theorem seed_work_rows_tail_of_raw_width (init : InputCfg n) (hn : 1 ≤ n)
    (s : ℕ) (ε : ℝ≥0∞)
    (hwidth : law init (workFailureAt init s (fun ω w => RawWidthRow init ω s w)) ≤
      ε * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)}) :
    law init (workFailureAt init s (fun ω w => FirstWorkRow init ω s w)) ≤
        ε * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} ∧
    law init (workFailureAt init s (fun ω w => SecondWorkRow init ω s w)) ≤
        ε * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} :=
  ⟨(seed_first_work_failure_le_raw_width init hn s).trans hwidth,
    (seed_second_work_failure_le_raw_width init hn s).trans hwidth⟩

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockWorkRows

end
