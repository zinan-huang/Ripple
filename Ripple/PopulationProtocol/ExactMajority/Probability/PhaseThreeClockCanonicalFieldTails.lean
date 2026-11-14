-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockCanonicalFieldTails.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockCanonicalRows
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockWorkRows

/-!
# Individual completed Core fields on the canonical seed fibre

The event has the exact first seed, SeedProfile, and AsyncEntry guards.
The generic null-event transfer uses the proved canonical passage
existence event. Each deterministic field is then stated separately at
the compiled virtualTimes witness. The shared raw_local n^(-8) theorem
is in CanonicalRows.

The two work-field inequalities are inclusions into the canonical
raw_width failure. No numerical raw_width tail is asserted here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockCanonicalFieldTails

open TimeTheorem PairLog StageEventSpec PhaseThreeClockProducer
  PhaseThreeClockVirtual PhaseThreeClockCore PhaseThreeClockRows
  PhaseThreeClockSeedTails PhaseThreeClockRawLocalRow PhaseThreeClockActivationRows
  PhaseThreeClockHourOccupancyRow PhaseThreeClockPassageOrderRows
  PhaseThreeClockCanonicalRows PhaseThreeClockWorkRows

variable {n : ℕ}

def canonicalFieldFailureAt (init : InputCfg n) (s : ℕ)
    (R : InputLog n → ℕ → ℕ → Prop) : Set (InputLog n) :=
  {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
    SeedProfile n init (trace init ω s) ∧
    ∃ T, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T ∧ ¬ R ω s T}

theorem seed_canonical_field_null (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 42 ≤ n) (s : ℕ)
    (R : InputLog n → ℕ → ℕ → Prop)
    (hR : ∀ ω T, ω ∈ seedPrefix init s → AsyncEntry init ω s T →
      PassageTimes init ω s (virtualTimes init ω s) → R ω s T) :
    law init (canonicalFieldFailureAt init s R) = 0 := by
  apply le_antisymm ?_ bot_le
  apply le_trans (measure_mono ?_)
    (le_of_eq (seed_canonical_passage_times_null init hc hn s))
  rintro ω ⟨hs, hp, T, hT, he, hbad⟩
  refine ⟨hs, hp, T, hT, he, ?_⟩
  intro hw
  exact hbad (hR ω T ⟨hs, hp⟩ he hw)

theorem seed_canonical_field_tail (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 42 ≤ n) (s : ℕ)
    (R : InputLog n → ℕ → ℕ → Prop)
    (hR : ∀ ω T, ω ∈ seedPrefix init s → AsyncEntry init ω s T →
      PassageTimes init ω s (virtualTimes init ω s) → R ω s T) :
    law init (canonicalFieldFailureAt init s R) ≤
      (0 : ℝ≥0∞) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  simp only [seed_canonical_field_null init hc hn s R hR, zero_mul, le_refl]

/-- The same deterministic transfer in the exact compiled row event. -/
theorem canonical_field_global_null (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 42 ≤ n)
    (R : InputLog n → ℕ → ℕ → Prop)
    (hR : ∀ ω s T, ω ∈ seedPrefix init s → AsyncEntry init ω s T →
      PassageTimes init ω s (virtualTimes init ω s) → R ω s T) :
    law init (PhaseThreeClockRows.rowFailure init R) = 0 := by
  apply le_antisymm ?_ bot_le
  apply le_trans (measure_mono ?_)
    (le_of_eq (canonical_passage_times_global_null init hc hn))
  rintro ω ⟨s, T, hs, hT, he, hbad⟩
  refine ⟨s, T, hs, hT, he, ?_⟩
  intro hw
  exact hbad (hR ω s T ⟨hs, he.seed_profile⟩ he hw)

theorem seed_canonical_activation_first_tail (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 42 ≤ n) (s : ℕ) :
    law init (canonicalFieldFailureAt init s
      (fun ω s T => ActivationFirstAt init ω s (virtualTimes init ω s).activation)) ≤
      (0 : ℝ≥0∞) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply seed_canonical_field_tail init hc hn s
  intro ω T hseed hentry hw
  exact hw.hours.1

theorem seed_canonical_first_zero_tail (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 42 ≤ n) (s : ℕ) :
    law init (canonicalFieldFailureAt init s
      (fun ω s T => (virtualTimes init ω s).first 0 = s)) ≤
      (0 : ℝ≥0∞) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply seed_canonical_field_tail init hc hn s
  intro ω T hseed hentry hw
  exact hw.first_zero

theorem seed_canonical_bulk_zero_tail (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 42 ≤ n) (s : ℕ) :
    law init (canonicalFieldFailureAt init s
      (fun ω s T => (virtualTimes init ω s).bulk 0 = s)) ≤
      (0 : ℝ≥0∞) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply seed_canonical_field_tail init hc hn s
  intro ω T hseed hentry hw
  exact hw.bulk_zero

theorem seed_canonical_level_first_tail (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 42 ≤ n) (s : ℕ) :
    law init (canonicalFieldFailureAt init s
      (fun ω s T => ∀ ell, 1 ≤ ell → ell ≤ clockTop n →
        firstAfter (fun v => 1 ≤ frontCountL init (virtualLabels init ω s)
          (virtualLabels init ω v) ell) s ((virtualTimes init ω s).first ell))) ≤
      (0 : ℝ≥0∞) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply seed_canonical_field_tail init hc hn s
  intro ω T hseed hentry hw
  exact hw.levels.1

theorem seed_canonical_level_bulk_tail (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 42 ≤ n) (s : ℕ) :
    law init (canonicalFieldFailureAt init s
      (fun ω s T => ∀ ell, 1 ≤ ell → ell ≤ clockTop n →
        firstAfter (fun v => bulkThreshold (clockCount (virtualCfg init ω s)) ≤
          frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) ell)
          s ((virtualTimes init ω s).bulk ell))) ≤
      (0 : ℝ≥0∞) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply seed_canonical_field_tail init hc hn s
  intro ω T hseed hentry hw
  exact hw.levels.2

theorem seed_canonical_start_zero_tail (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 42 ≤ n) (s : ℕ) :
    law init (canonicalFieldFailureAt init s
      (fun ω s T => (virtualTimes init ω s).start 0 = (virtualTimes init ω s).activation)) ≤
      (0 : ℝ≥0∞) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply seed_canonical_field_tail init hc hn s
  intro ω T hseed hentry hw
  exact hw.hours.2.1

theorem seed_canonical_start_positive_tail (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 42 ≤ n) (s : ℕ) :
    law init (canonicalFieldFailureAt init s
      (fun ω s T => ∀ h, 1 ≤ h → h ≤ PhaseThreeModel.Numeric.hourIndex n →
        firstAfter (fun v => highThreshold (clockCount (virtualCfg init ω s)) ≤
          frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) (256 * h))
          s ((virtualTimes init ω s).start h))) ≤
      (0 : ℝ≥0∞) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply seed_canonical_field_tail init hc hn s
  intro ω T hseed hentry hw
  exact hw.hours.2.2.1

theorem seed_canonical_finish_first_tail (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 42 ≤ n) (s : ℕ) :
    law init (canonicalFieldFailureAt init s
      (fun ω s T => ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
        firstAfter (fun v => smallThreshold (clockCount (virtualCfg init ω s)) ≤
          frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) (256 * (h + 1)))
          s ((virtualTimes init ω s).finish h))) ≤
      (0 : ℝ≥0∞) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply seed_canonical_field_tail init hc hn s
  intro ω T hseed hentry hw
  exact hw.hours.2.2.2

theorem seed_canonical_cap_first_tail (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 42 ≤ n) (s : ℕ) :
    law init (canonicalFieldFailureAt init s
      (fun ω s T => CapFirstAt init ω s (virtualTimes init ω s).cap)) ≤
      (0 : ℝ≥0∞) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply seed_canonical_field_tail init hc hn s
  intro ω T hseed hentry hw
  exact hw.cap

theorem seed_canonical_exact_hour_tail (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 42 ≤ n) (s : ℕ) :
    law init (canonicalFieldFailureAt init s
      (fun ω s T => ExactHourRow init ω s (virtualTimes init ω s))) ≤
      (0 : ℝ≥0∞) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply seed_canonical_field_tail init hc hn s
  intro ω T hseed hentry hw
  exact exact_hour_row_of_passages init ω s T (virtualTimes init ω s) hseed hentry hw.hours

theorem seed_canonical_previous_end_tail (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 42 ≤ n) (s : ℕ) :
    law init (canonicalFieldFailureAt init s
      (fun ω s T => PreviousEndRow init (virtualTimes init ω s))) ≤
      (0 : ℝ≥0∞) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply seed_canonical_field_tail init hc hn s
  intro ω T hseed hentry hw
  exact previous_end_row_of_passages init (by omega) ω s T (virtualTimes init ω s) hseed hentry hw.hours

theorem seed_canonical_active_main_floor_tail (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 42 ≤ n) (s : ℕ) :
    law init (canonicalFieldFailureAt init s
      (fun ω s T => ActiveMainRow init ω s (virtualTimes init ω s))) ≤
      (0 : ℝ≥0∞) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply seed_canonical_field_tail init hc hn s
  intro ω T hseed hentry hw
  exact (active_role_rows_of_activationFirst init ω s (virtualTimes init ω s) hseed hw.hours.1).1

theorem seed_canonical_active_clock_floor_tail (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 42 ≤ n) (s : ℕ) :
    law init (canonicalFieldFailureAt init s
      (fun ω s T => ActiveClockRow init ω s (virtualTimes init ω s))) ≤
      (0 : ℝ≥0∞) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply seed_canonical_field_tail init hc hn s
  intro ω T hseed hentry hw
  exact (active_role_rows_of_activationFirst init ω s (virtualTimes init ω s) hseed hw.hours.1).2

theorem seed_canonical_activation_before_cap_tail (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 42 ≤ n) (s : ℕ) :
    law init (canonicalFieldFailureAt init s
      (fun ω s T => ActivationBeforeCapRow init (virtualTimes init ω s))) ≤
      (0 : ℝ≥0∞) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply seed_canonical_field_tail init hc hn s
  intro ω T hseed hentry hw
  exact (passage_order_rows init (by omega) ω s T (virtualTimes init ω s) hseed hentry hw).1

theorem seed_canonical_all_before_cap_tail (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 42 ≤ n) (s : ℕ) :
    law init (canonicalFieldFailureAt init s
      (fun ω s T => AllBeforeCapRow init T (virtualTimes init ω s))) ≤
      (0 : ℝ≥0∞) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply seed_canonical_field_tail init hc hn s
  intro ω T hseed hentry hw
  exact (passage_order_rows init (by omega) ω s T (virtualTimes init ω s) hseed hentry hw).2.1

theorem seed_canonical_level_before_cap_tail (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 42 ≤ n) (s : ℕ) :
    law init (canonicalFieldFailureAt init s
      (fun ω s T => LevelBeforeCapRow init (virtualTimes init ω s))) ≤
      (0 : ℝ≥0∞) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply seed_canonical_field_tail init hc hn s
  intro ω T hseed hentry hw
  exact (passage_order_rows init (by omega) ω s T (virtualTimes init ω s) hseed hentry hw).2.2.1

theorem seed_canonical_hour_before_cap_tail (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 42 ≤ n) (s : ℕ) :
    law init (canonicalFieldFailureAt init s
      (fun ω s T => HourBeforeCapRow init (virtualTimes init ω s))) ≤
      (0 : ℝ≥0∞) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply seed_canonical_field_tail init hc hn s
  intro ω T hseed hentry hw
  exact (passage_order_rows init (by omega) ω s T (virtualTimes init ω s) hseed hentry hw).2.2.2

theorem seed_canonical_first_work_failure_le_raw_width (init : InputCfg n)
    (hn : 1 ≤ n) (s : ℕ) :
    law init (canonicalFieldFailureAt init s
      (fun ω s _T => FirstWorkRow init ω s (virtualTimes init ω s))) ≤
    law init (canonicalFieldFailureAt init s
      (fun ω s _T => RawWidthRow init ω s (virtualTimes init ω s))) := by
  apply measure_mono
  rintro ω ⟨hs, hp, T, hT, he, hbad⟩
  refine ⟨hs, hp, T, hT, he, ?_⟩
  intro hwidth
  exact hbad (work_rows_of_rawWidth init hn ω s (virtualTimes init ω s)
    ⟨hs, hp⟩ hwidth).1

theorem seed_canonical_second_work_failure_le_raw_width (init : InputCfg n)
    (hn : 1 ≤ n) (s : ℕ) :
    law init (canonicalFieldFailureAt init s
      (fun ω s _T => SecondWorkRow init ω s (virtualTimes init ω s))) ≤
    law init (canonicalFieldFailureAt init s
      (fun ω s _T => RawWidthRow init ω s (virtualTimes init ω s))) := by
  apply measure_mono
  rintro ω ⟨hs, hp, T, hT, he, hbad⟩
  refine ⟨hs, hp, T, hT, he, ?_⟩
  intro hwidth
  exact hbad (work_rows_of_rawWidth init hn ω s (virtualTimes init ω s)
    ⟨hs, hp⟩ hwidth).2

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockCanonicalFieldTails

end
